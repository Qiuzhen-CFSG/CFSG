module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.NormalizerModels.Marking
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.NormalizerModels.QuotientTransfer

/-!
# Marked model transfers for the graph-field normalizer

`Marking` constructs the actual perfect central cover and identifies the
image of O²(C_L(r)) with the diagonal-and-cycle E₉. `QuotientTransfer`
embeds the relative quotient N_G(L)/C_G(L) in the actual automorphism
group, preserving the inner subgroup and outer involution.

The source normalizer witnesses are not yet constructed. Their remaining
model inputs are the centerless quaternion complement and fusion, the
center-C₂ cover normalizer and action, and the full automorphism pointwise
fixer and quaternion placement calculations. The conditional fixer and
placement transfers do not discharge these inputs.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the graph-field branch of 16.4.9(2), printed pp.1191–1192.
-/
