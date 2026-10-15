import { DynamoDBClient } from '@aws-sdk/client-dynamodb';
import { DynamoDBDocumentClient, PutCommand, GetCommand, DeleteCommand, UpdateCommand } from '@aws-sdk/lib-dynamodb';

export class DynamoStore {
  constructor(table,client=DynamoDBDocumentClient.from(new DynamoDBClient({}))) {
    if (!table) throw new Error('Session table is required.');
    this.table=table; this.client=client;
  }
  async put(pk,value) {
    await this.client.send(new PutCommand({TableName:this.table,Item:{...value,pk,ttl:Math.ceil(value.expires/1000)},ConditionExpression:'attribute_not_exists(pk)'}));
  }
  async get(pk) {
    return (await this.client.send(new GetCommand({TableName:this.table,Key:{pk},ConsistentRead:true}))).Item || null;
  }
  async consume(pk) {
    try {
      return (await this.client.send(new DeleteCommand({TableName:this.table,Key:{pk},ConditionExpression:'attribute_exists(pk) AND expires > :now',ExpressionAttributeValues:{':now':Date.now()},ReturnValues:'ALL_OLD'}))).Attributes || null;
    } catch(error) { if(error.name==='ConditionalCheckFailedException')return null; throw error; }
  }
  async remove(pk) { await this.client.send(new DeleteCommand({TableName:this.table,Key:{pk}})); }
  async claimPost(pk,now) {
    try {
      await this.client.send(new UpdateCommand({TableName:this.table,Key:{pk},UpdateExpression:'SET lastPost = :now',ConditionExpression:'expires > :now AND (attribute_not_exists(lastPost) OR lastPost <= :cutoff)',ExpressionAttributeValues:{':now':now,':cutoff':now-5000}}));
      return true;
    } catch(error) { if(error.name==='ConditionalCheckFailedException')return false; throw error; }
  }
}
