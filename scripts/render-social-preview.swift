// Regenerate the checked-in social card on macOS:
// swift scripts/render-social-preview.swift assets/social-preview.png
// This is a build-time design source; the website only serves the resulting PNG.
import AppKit
import CoreText

let width = 1200
let height = 630
let output = CommandLine.arguments.dropFirst().first ?? "assets/social-preview.png"
let context = CGContext(
    data: nil, width: width, height: height, bitsPerComponent: 8,
    bytesPerRow: width * 4, space: CGColorSpace(name: CGColorSpace.sRGB)!,
    bitmapInfo: CGImageAlphaInfo.noneSkipLast.rawValue
)!
context.setAllowsAntialiasing(true)
context.setShouldAntialias(true)

func color(_ hex: UInt32) -> NSColor {
    NSColor(srgbRed: CGFloat((hex >> 16) & 255) / 255,
            green: CGFloat((hex >> 8) & 255) / 255,
            blue: CGFloat(hex & 255) / 255, alpha: 1)
}

@discardableResult
func text(_ value: String, x: CGFloat, baseline: CGFloat, size: CGFloat,
          font: String = "Georgia", ink: UInt32 = 0xedf1fa, kern: CGFloat = 0) -> CGFloat {
    let attributed = NSAttributedString(string: value, attributes: [
        .font: NSFont(name: font, size: size)!,
        .foregroundColor: color(ink), .kern: kern
    ])
    let line = CTLineCreateWithAttributedString(attributed)
    let bounds = CTLineGetBoundsWithOptions(line, .useGlyphPathBounds)
    precondition(x + bounds.maxX < CGFloat(width - 60), "Text exceeds the card's safe area")
    context.textPosition = CGPoint(x: x, y: CGFloat(height) - baseline)
    CTLineDraw(line, context)
    return bounds.width
}

context.setFillColor(color(0x070e20).cgColor)
context.fill(CGRect(x: 0, y: 0, width: width, height: height))

// The same Georgia italic mark and pale ink used by the website.
text("h.", x: 92, baseline: 407, size: 320, font: "Georgia-Italic", kern: -24)

context.setStrokeColor(color(0x35415a).cgColor)
context.setLineWidth(1)
context.move(to: CGPoint(x: 393, y: 172))
context.addLine(to: CGPoint(x: 393, y: 458))
context.strokePath()

let lines = [
    "Open autoresearch targeting",
    "the generalized Hodge conjecture",
    "for sextic fourfolds",
    "with an involution."
]
for (index, line) in lines.enumerated() {
    text(line, x: 448, baseline: CGFloat(227 + index * 57), size: 40)
}
text("hodge.computer", x: 92, baseline: 548, size: 24,
     font: "HelveticaNeue", ink: 0x9cacc5, kern: 0.6)

let image = NSBitmapImageRep(cgImage: context.makeImage()!)
let png = image.representation(using: .png, properties: [:])!
try png.write(to: URL(fileURLWithPath: output))
print("Wrote \(output): \(width) × \(height), \(png.count) bytes")
