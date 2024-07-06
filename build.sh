# Rebuilds the bcgen.mtw.sml and example.mtw.sml files
# mlton, smlfmt, and smlgen must be installed and accessible in the PATH.
mlton mltwig.mlb
./mltwig bcgen.mtw
./mltwig example.mtw
smlfmt bcgen.mtw.sml example.mtw.sml --force
smlgen --test example.mtw.sml TreeProcessor.User.result:s TreeProcessor.User.tree:s TreeProcessor.User.instr:s TreeProcessor.User.symbol:s
rm example.mtw.sml
mv example.mtw.sml.test example.mtw.sml