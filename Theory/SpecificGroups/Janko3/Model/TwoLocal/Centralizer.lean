module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Generators
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.Intrinsic

/-!
# Certified orders and characteristic two for the J₃ local candidate

The fixed Sylow candidate has order 128 and the fixed centralizer candidate
has order 1920. Short stabilizer chains certify both orders in the original
6156-point ATLAS action. Inside the latter candidate, five explicit words
generate a normal subgroup of order 32. Its intrinsic centralizer is contained
in its order-two center, so the local two-core is self-centralizing.

These are finite-subgroup calculations for the word-defined candidates. The
normalizer-coverage and ambient Sylow identification arguments belong to the
quasithin converse assembly. No ambient order or simplicity assertion is used.

Source: GLS, volume 3, Table 5.3h, printed p.269. The application is
Aschbacher–Smith, Theorem 0.1.2(5), printed p.4. Discovery data and the untrusted
certificate generators are retained under `Centralizer/source/`.
-/
