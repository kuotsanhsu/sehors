
#include <print>
int main() {
	constexpr auto s = R"(
#include <print>
int main() {{
	constexpr auto s = R"({}{}";
	std::print(s, s, ')');
}}
)";
	std::print(s, s, ')');
}
