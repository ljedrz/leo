function main(s: bool, a: i64, b: i64, c: i64) {
    let r = if s ? a : b;

    console.assert(r == c);
}