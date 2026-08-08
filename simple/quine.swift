import Foundation
@main
struct Hello {
    static func main() {
        let s = #"""
import Foundation
@main
struct Hello {
    static func main() {
        let s = #"""
%@
"""%@
        print(String(format: s, s, "#"))
    }
}
"""#
        print(String(format: s, s, "#"))
    }
}
