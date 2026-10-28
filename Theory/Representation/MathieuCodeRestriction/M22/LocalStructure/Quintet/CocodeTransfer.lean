module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.Quotients
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.FourGeneration
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.NaturalQuotient
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.TransvectionFactors.ChiefFactors
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.TransvectionFactors.Hyperplanes

/-!
# The conditional cocode transfer for the outer M22 quintet

Native tetrad parity and the actual action on the five remaining sextet parts
identify the top quotient with the natural S5 module. Its proved irreducibility
discharges the intermediate premise in the transvection branch, yielding the
strict chief flag, dimensions, and equivariant duality with the actual kernel
under conjugation. The constructed flag and action data feed the subsequent
code-duality proof directly.

The common four-subgroup of the compatible octad and sextet kernels fixes five
dimensions in U7 by the faithful sextet transvections. The earlier ambient fixed
dimension six supplies a vector outside V6, proving four-subgroup generation
and hence the hyperplane xi clause. Earlier involution data give fixed dimension
two for every hyperplane. The explicit cubic datum is also checked against the
geometric S5 marking: its four fixed dimensions split as two in V6 and two above.

Only earlier M24, H.14 group/action, and involution/cubic facts remain inputs to
`transfer_of_earlier_data`. Their instantiation belongs to the source assembly;
no requested M22 flag, action, fixed dimension or generation clause is assumed.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
H.15.4, printed p.400, using H.15.2(5), H.15.3 and H.14.
-/

public section

noncomputable section
open scoped IsMulCommutative
open Representation.BinaryOffender
namespace MathieuCode.M22Quintet.CocodeTransfer

/-- Only the ambient sextet displacement law and the elementary order bound
are needed to generate the geometric middle space by four-subgroup fixed spaces. -/
theorem V6_le_fourFixedSpan_of_sextet_displacement
    [IsElementaryAbelian 2 K] (hK : 8 ≤ Nat.card K)
    (hKS : K ≤ KS.comap m22PairStabilizer.subtype)
    (hmove : ∀ k ∈ KS, ∀ u ∈ U7, cocodeRepresentation k u - u ∈ U1) :
    V6 ≤ fourFixedSpan m22OuterCocodeRepresentation K := by
  intro v hv
  apply mem_fourFixedSpan_of_line_displacement m22OuterCocodeRepresentation K hK W1 finrank_W1
  · intro w hw k
    exact W1_fixed ⟨k.val, Subgroup.map_subtype_le _ k.property⟩ w hw
  · intro k
    exact displacement_mem_W1 k.val (hmove k.val.val (hKS k.property)) v hv

/-- Generation from earlier M24 fixed-space data and the top-factor
irreducibility, which the S5 marking branch must supply separately. -/
theorem fourFixedSpan_eq_top_of_sextet_data
    [IsElementaryAbelian 2 K] (hK : 8 ≤ Nat.card K)
    (hKS : K ≤ KS.comap m22PairStabilizer.subtype)
    (hmove : ∀ k ∈ KS, ∀ u ∈ U7, cocodeRepresentation k u - u ∈ U1)
    (hEK : E ≤ K) (hE : IsElementaryAbelian 2 E) (hcard : Nat.card E = 4)
    (hfixed : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation E24) = 6)
    (hmiddle : Module.finrank (ZMod 2)
      (fixedSpace cocodeRepresentation E24 ⊓ U7 : Submodule (ZMod 2) Cocode) = 5)
    [Representation.IsIrreducible V6Subrepresentation.quotientRepresentation] :
    fourFixedSpan m22OuterCocodeRepresentation K = ⊤ :=
  fourFixedSpan_eq_top_of_middle_and_escape m22OuterCocodeRepresentation K Q
    Q_le_normalizer_K V6Subrepresentation
    (V6_le_fourFixedSpan_of_sextet_displacement hK hKS hmove)
    E hEK hE hcard (common_fixedSpace_not_le_V6 hfixed hmiddle)

/-- The xi conclusion for every relative-index-two subgroup follows from
the four-subgroup generation just established. -/
theorem fixedSpaceSpan_eq_top_of_sextet_data
    [IsElementaryAbelian 2 K] (hK : 8 ≤ Nat.card K)
    (hKS : K ≤ KS.comap m22PairStabilizer.subtype)
    (hmove : ∀ k ∈ KS, ∀ u ∈ U7, cocodeRepresentation k u - u ∈ U1)
    (hEK : E ≤ K) (hE : IsElementaryAbelian 2 E) (hcard : Nat.card E = 4)
    (hfixed : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation E24) = 6)
    (hmiddle : Module.finrank (ZMod 2)
      (fixedSpace cocodeRepresentation E24 ⊓ U7 : Submodule (ZMod 2) Cocode) = 5)
    [Representation.IsIrreducible V6Subrepresentation.quotientRepresentation]
    (A : Subgroup m22PairStabilizer) (hindex : A.relIndex K = 2) :
    fixedSpaceSpan m22OuterCocodeRepresentation A = ⊤ :=
  fixedSpaceSpan_eq_top_of_fourFixedSpan _ hindex
    (fourFixedSpan_eq_top_of_sextet_data hK hKS hmove hEK hE hcard hfixed hmiddle)

/-- Construct the native chief flag, discharging top irreducibility by the
actual sextet-part action and the earlier H.14 quotient identification. -/
@[expose] def chiefFlagOfEarlierData [IsElementaryAbelian 2 K]
    (D : SextetTransvectionInputs) (I : InnerInputs)
    [Representation.IsIrreducible (innerConjugation I)]
    (hpart : NaturalQuotient.partAction.ker = pCore 2 Q)
    (e : (Q ⧸ pCore 2 Q) ≃* Equiv.Perm (Fin 5)) : DualAction.CocodeFlag := by
  letI := NaturalQuotient.top_isIrreducible hpart e
  exact cocodeChiefFlag D I

/-- Supply the full cocode interface used by code duality. The group-module
carrier is literally Additive K, its marking is the identity on K, and both
linear equivalences intertwine the native Q actions. -/
@[expose] def actionDataOfEarlierData [IsElementaryAbelian 2 K]
    (D : SextetTransvectionInputs) (I : InnerInputs)
    [Representation.IsIrreducible (innerConjugation I)]
    (hpart : NaturalQuotient.partAction.ker = pCore 2 Q)
    (e : (Q ⧸ pCore 2 Q) ≃* Equiv.Perm (Fin 5)) :
    DualAction.CocodeActionData (chiefFlagOfEarlierData D I hpart e) (Additive K) where
  kernelAction := kernelConjugation
  kernelMarking :=
    { toFun := fun k => k.toAdd.toMul
      invFun := fun k => Multiplicative.ofAdd (Additive.ofMul k)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  kernelMarking_equivariant := fun _ _ => rfl
  kernel_dim := finrank_kernel D
  middleEquiv := middleDuality D
  middleEquiv_equivariant := middleDuality_equivariant D
  quotientMap := NaturalQuotient.q
  quotientMap_surjective := NaturalQuotient.q_surjective hpart e
  quotientMap_ker := NaturalQuotient.q_ker hpart
  naturalQuotient := NaturalQuotient.marking
  naturalQuotient_equivariant := NaturalQuotient.marking_equivariant
  centerAction_faithful := kernelAction_faithful D
  centerAction_full := kernelAction_full_intrinsic D

/-- All cocode clauses from the earlier native sextet/octad and H.14 data.
The chief flag and its genuine action identifications are constructed here;
the top irreducibility and common-four middle dimension are both discharged.
The last clause records compatibility with the source order-three datum. -/
theorem transfer_of_earlier_data
    [IsElementaryAbelian 2 K] (D : SextetTransvectionInputs) (I : InnerInputs)
    [Representation.IsIrreducible (innerConjugation I)]
    (hpart : NaturalQuotient.partAction.ker = pCore 2 Q)
    (e : (Q ⧸ pCore 2 Q) ≃* Equiv.Perm (Fin 5))
    (hindecomp : ∀ U W : Subrepresentation kernelConjugation,
      IsCompl U W → U = ⊥ ∨ W = ⊥)
    (i0 : m22PairStabilizer) (hi0 : i0 ∈ K) (hout : i0 ∉ L)
    (horder : orderOf i0 = 2)
    (hfixed : Module.finrank (ZMod 2)
      (fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers i0)) = 5)
    (hEK : E ≤ K) (hE : IsElementaryAbelian 2 E) (hcard : Nat.card E = 4)
    [IsElementaryAbelian 2 E24] (hcard24 : Nat.card E24 = 4)
    (hcommon : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation E24) = 6)
    (hcubic : ∀ g : Q, orderOf g = 3 → Module.finrank (ZMod 2)
      (fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers g.val)) = 4) :
    (∃ F : DualAction.CocodeFlag, Nonempty (DualAction.CocodeActionData F (Additive K))) ∧
    W1 = V1 ∧
    ((⊥ : Submodule (ZMod 2) M22Cocode) < V1 ∧ V1 < V2 ∧ V2 < V6 ∧ V6 < ⊤) ∧
    (Module.finrank (ZMod 2) V1 = 1 ∧ Module.finrank (ZMod 2) V2 = 2 ∧
      Module.finrank (ZMod 2) V6 = 6) ∧
    fourFixedSpan m22OuterCocodeRepresentation K = ⊤ ∧
    (∀ A : Subgroup m22PairStabilizer, A ≤ K → A.relIndex K = 2 →
      fixedSpaceSpan m22OuterCocodeRepresentation A = ⊤ ∧
        Module.finrank (ZMod 2) (fixedSpace m22OuterCocodeRepresentation A) = 2) ∧
    (∀ g : Q, orderOf g = 3 →
      Module.finrank (ZMod 2) (fixedSpace V6Subrepresentation.toRepresentation
        (Subgroup.zpowers g)) = 2 ∧
      Module.finrank (ZMod 2) (fixedSpace V6Subrepresentation.quotientRepresentation
        (Subgroup.zpowers g)) = 2) := by
  let := NaturalQuotient.top_isIrreducible hpart e
  have hgen := fourFixedSpan_eq_top_of_sextet_data
    (by rw [D.card_kernel]; decide) D.kernel_le D.displacement hEK hE hcard hcommon
    (finrank_common_middle_fixed D hcard24)
  refine ⟨⟨chiefFlagOfEarlierData D I hpart e,
    ⟨actionDataOfEarlierData D I hpart e⟩⟩, W1_eq_V1 D I,
    cocode_flag_strict D I, ⟨finrank_V1 D I, finrank_V2 D I, finrank_V6⟩,
    hgen, ?_, ?_⟩
  · intro A hA hindex
    exact ⟨fixedSpaceSpan_eq_top_of_fourFixedSpan _ hindex hgen,
      finrank_fixed_hyperplane D I hindecomp i0 hi0 hout horder hfixed A hA hindex⟩
  · intro g hg
    exact NaturalQuotient.source_cubic_fixed_dimensions hpart g hg (hcubic g hg)

end MathieuCode.M22Quintet.CocodeTransfer
