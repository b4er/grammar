# awk -f table.awk results.tsv
#
# Rows CASE PARSER METRIC VALUE as a table: one line per case and parser, one
# column per metric, both in the order of their first appearance.
BEGIN { FS = "\t" }
/^#/ || NF < 4 { next }
{
  k = $1 SUBSEP $2
  if (!(k in seen)) { seen[k] = 1; keys[++nk] = k }
  if (!($3 in col)) { col[$3] = ++nm; metric[nm] = $3 }
  val[k, $3] = $4
}
END {
  w1 = length("case"); w2 = length("parser")
  for (i = 1; i <= nk; i++) {
    split(keys[i], p, SUBSEP)
    if (length(p[1]) > w1) w1 = length(p[1])
    if (length(p[2]) > w2) w2 = length(p[2])
  }
  for (j = 1; j <= nm; j++) {
    w[j] = length(metric[j])
    for (i = 1; i <= nk; i++)
      if (length(val[keys[i], metric[j]]) > w[j]) w[j] = length(val[keys[i], metric[j]])
  }
  printf "%-*s  %-*s", w1, "case", w2, "parser"
  for (j = 1; j <= nm; j++) printf "  %*s", w[j], metric[j]
  printf "\n"
  for (i = 1; i <= nk; i++) {
    split(keys[i], p, SUBSEP)
    printf "%-*s  %-*s", w1, p[1], w2, p[2]
    for (j = 1; j <= nm; j++) printf "  %*s", w[j], val[keys[i], metric[j]]
    printf "\n"
  }
}
