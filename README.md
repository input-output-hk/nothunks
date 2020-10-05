# nothunks

[![GitHub CI](https://github.com/input-output-hk/nothunks/workflows/CI/badge.svg)](https://github.com/input-output-hk/nothunks/actions)

Long lived application data typically should not contain any thunks. This
library can be used to examine values for unexpected thunks, which can then be
used in assertions. This can be invaluable in avoiding memory leaks, or tracking
down existing ones.

See my presentation
[MuniHac 2020: Being lazy without being bloated](https://www.youtube.com/watch?v=7t6wt7ByBWg)
for an overview, motivating the library and explaining how it is intended to be
used and how it works internally.
