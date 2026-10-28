module

public import CFSG.Quasithin.ChapterE.Section03.Offenders
public import Theory.GroupTheory.AbelianGeneratorCore
public import Theory.Representation.BinaryOffender.CentralSectionAction

/-!
# Rank and fixed-subgroup deductions for the canonical offender

Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §8.2.1, printed pp.714–717 (PDF pp.731–734).

The subgroup A is the literal normalizer of V in a conjugate, and its bar
is its image in the conjugation automizer of V. Quotient-rank additivity
identifies m(V/Z_I) with the corank of A plus its image rank. In the code
cases that corank is one. The non-FF condition forces the fixed corank to
be strictly larger than the image rank, so C_V(A) = Z_I. The fundamental
weak-closure inequality then gives the numerical code rows. The same rank
identity and H.4.4(3) give the Hermitian rank saturation in 8.2.4.

Normality of the actor image under the actual image of T makes C_V(A)
normal in T. Once C_V(A) = V ∩ Vᵍ, both abelian generators of I centralize
it. These statements retain relative normality, without asserting normality
in the ambient group. Here Vᵍ is the left conjugate g V g⁻¹; the source's
right-conjugating element is g⁻¹.

These are conditional deductions, not the complete Propositions 8.2.2–5.
The two-conjugate existence/classification and action kernel come from E.2;
the non-FF and model estimates come from B.4 and H.4/H.16. The code row
lower bounds, w = k, the actual model identifications and marked actors,
and the exclusion n > 1 must still be supplied in the source assembly.
-/

public section

namespace CFSG.Quasithin.Chapter8.Section02.Offenders
open Subgroup Representation.BinaryOffender ChapterE
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

private theorem rank_add_corank {V U : Subgroup G} [IsElementaryAbelian 2 V]
    (hUV : U ≤ V) : subgroupCorank V U + rank U = rank V := by
  have h := offender_corank_add (W := V) (A := U) (B := ⊥) bot_le hUV
  simpa only [subgroupCorank, relIndex_bot_left, rank] using h.symm

private theorem eq_of_corank_eq {V U Z : Subgroup G} [IsElementaryAbelian 2 V]
    (hZU : Z ≤ U) (hUV : U ≤ V) (hc : subgroupCorank V Z = subgroupCorank V U) :
    Z = U := by
  let _ : IsElementaryAbelian 2 U := offender_elementary_of_le hUV
  have h := offender_corank_add hZU hUV
  exact subgroup_eq_of_corank_zero hZU (by omega)

omit [Finite G] in
/-- The intersection Z_I is contained in the fixed subgroup of the actual offender normalizer. -/
theorem intersection_le_fixed (V : Subgroup G) [IsElementaryAbelian 2 V] (g : G) :
    V ⊓ V.map (MulAut.conj g).toMonoidHom ≤
      V ⊓ centralizer (offenderNormalizer V g : Set G) := by
  let W := V.map (MulAut.conj g).toMonoidHom
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  exact le_inf inf_le_left ((inf_le_right.trans W.le_centralizer).trans
    (centralizer_le (show offenderNormalizer V g ≤ W from inf_le_left)))

/-- The additive rank identity used in 8.2.2(7) and 8.2.5. The action-kernel equality is the preceding E.2 input; the coranks use the literal conjugate and its normalizer. -/
theorem intersection_corank (V : Subgroup G) [IsElementaryAbelian 2 V] (g : G)
    (hkernel : offenderNormalizer V g ⊓ centralizer (V : Set G) =
      V ⊓ V.map (MulAut.conj g).toMonoidHom) :
    subgroupCorank V (V ⊓ V.map (MulAut.conj g).toMonoidHom) =
      subgroupCorank (V.map (MulAut.conj g).toMonoidHom) (offenderNormalizer V g) +
        rank (inducedAutomizer V (offenderNormalizer V g)) := by
  let W := V.map (MulAut.conj g).toMonoidHom
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hV := rank_add_corank (V := V) (U := V ⊓ W) inf_le_left
  have hW := rank_add_corank (V := W) (U := V ⊓ W) inf_le_right
  have hr : rank W = rank V := by
    dsimp only [rank, W]
    rw [card_map_of_injective (MulAut.conj g).injective]
  have h := offender_centralizer_corank V g
  rw [hkernel] at h
  dsimp only [W] at hV hW hr
  omega

/-- For a non-FF module and a nontrivial actor image of corank one, the kernel identity forces C_V(A) = Z_I. This is the equality argument in the two code rows of 8.2.5. -/
theorem fixed_eq_intersection_of_nonFF (V : Subgroup G) [IsElementaryAbelian 2 V]
    (g : G) (hFF : ¬ IsFFModule (automizerRepresentation V))
    (hpos : 0 < rank (inducedAutomizer V (offenderNormalizer V g)))
    (hkernel : offenderNormalizer V g ⊓ centralizer (V : Set G) =
      V ⊓ V.map (MulAut.conj g).toMonoidHom)
    (hcorank : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (offenderNormalizer V g) = 1) :
    V ⊓ centralizer (offenderNormalizer V g : Set G) =
      V ⊓ V.map (MulAut.conj g).toMonoidHom := by
  have hz := intersection_corank V g hkernel
  rw [hcorank] at hz
  have hZU := intersection_le_fixed V g
  have hsum := offender_corank_add hZU (show
    V ⊓ centralizer (offenderNormalizer V g : Set G) ≤ V from inf_le_left)
  have hlt : rank (inducedAutomizer V (offenderNormalizer V g)) <
      subgroupCorank V (V ⊓ centralizer (offenderNormalizer V g : Set G)) := by
    rw [← fixedCodim_inducedAutomizer V (offenderNormalizer V g) inf_le_right]
    apply Nat.lt_of_not_ge
    intro hle
    apply hFF
    refine ⟨inducedAutomizer V (offenderNormalizer V g), ⟨?_,
      offender_inducedAutomizer_elementary V g⟩, hle⟩
    intro hb
    rw [hb, Representation.BinaryOffender.rank_bot] at hpos
    omega
  exact (eq_of_corank_eq hZU inf_le_left (by omega)).symm

omit [Finite G] in
/-- Normalization of the actual actor image suffices to normalize its fixed subgroup. No lift of actor-image normality to normality of A is assumed. -/
theorem fixed_normalized_of_image_normalized (V A T : Subgroup G)
    [IsElementaryAbelian 2 V]
    (hAN : A ≤ normalizer (V : Set G)) (hTN : T ≤ normalizer (V : Set G))
    (himage : inducedAutomizer V T ≤ normalizer (inducedAutomizer V A : Set (Automizer V))) :
    T ≤ normalizer (V ⊓ centralizer (A : Set G) : Subgroup G) := by
  have hstable := fixedSpace_stable_of_normalizes (automizerRepresentation V) himage
  have hconj : ∀ t ∈ T, ∀ v ∈ V ⊓ centralizer (A : Set G),
      t * v * t⁻¹ ∈ V ⊓ centralizer (A : Set G) := by
    intro t ht v hv
    let tN : normalizer (V : Set G) := ⟨t, hTN ht⟩
    let tbar : Automizer V := V.normalizerMonoidHom.rangeRestrict tN
    have htbar : tbar ∈ inducedAutomizer V T := ⟨tN, ht, rfl⟩
    let vV : V := ⟨v, hv.1⟩
    have hfix := (mem_fixedSpace_inducedAutomizer V A hAN (Additive.ofMul vV)).mpr hv.2
    have hfix' := (hstable htbar (Additive.ofMul vV)).2 hfix
    have hc := (mem_fixedSpace_inducedAutomizer V A hAN _).mp hfix'
    exact ⟨(mem_normalizer_iff.mp (hTN ht) v).mp hv.1, hc⟩
  intro t ht
  rw [mem_normalizer_iff]
  intro v
  constructor
  · exact hconj t ht v
  · intro hv
    have h := hconj t⁻¹ (T.inv_mem ht) _ hv
    simpa only [inv_inv, inv_mul_cancel_left, mul_inv_cancel_right, mul_assoc,
      inv_mul_cancel, mul_one] using h

omit [Finite G] in
/-- The relative-normality conclusion U normal in T, from normalization of the image of A by the image of T. -/
theorem fixed_normal_in_sylow (V A : Subgroup G) (T : Sylow 2 G)
    [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hAN : A ≤ normalizer (V : Set G))
    (hTN : (T : Subgroup G) ≤ normalizer (V : Set G))
    (himage : inducedAutomizer V T ≤ normalizer (inducedAutomizer V A : Set (Automizer V))) :
    ((V ⊓ centralizer (A : Set G)).subgroupOf T).Normal :=
  (normal_subgroupOf_iff_le_normalizer (inf_le_left.trans hVT)).mpr
    (fixed_normalized_of_image_normalized V A T hAN hTN himage)

omit [Finite G] in
/-- The actual two-conjugate subgroup centralizes U once the fixed-subgroup equality is established. -/
theorem generated_pair_centralizes_fixed (V : Subgroup G) [IsElementaryAbelian 2 V]
    (g : G) (hfixed : V ⊓ centralizer (offenderNormalizer V g : Set G) =
      V ⊓ V.map (MulAut.conj g).toMonoidHom) :
    V ⊔ V.map (MulAut.conj g).toMonoidHom ≤
      centralizer (V ⊓ centralizer (offenderNormalizer V g : Set G) : Subgroup G) := by
  let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  rw [hfixed]
  exact sup_le_centralizer_inf_of_abelian V _

/-- The numerical code-row deduction in 8.2.5. Set d = 5 for the M22 code and d = 6 for the M24 code. The M24 bound r ≥ 7 includes the separate E.6.11/H.16.6 exclusion of r = 6; it is not proved here. No module identification is asserted by these numerical hypotheses. -/
theorem code_row_parameters (V : Subgroup G) [IsElementaryAbelian 2 V]
    (T : Sylow 2 G) (g : G) (hT : HypothesisE322 V T)
    (hFF : ¬ IsFFModule (automizerRepresentation V)) (hOff : IsWOffenderAt V T g)
    (hw : globalW V T = 1) (d : ℕ) (hd : 0 < d)
    (hr : ((d + 1 : ℕ) : ℕ∞) ≤ globalR V)
    (hm : primeRank 2 (Automizer V) ≤ d)
    (hkernel : offenderNormalizer V g ⊓ centralizer (V : Set G) =
      V ⊓ V.map (MulAut.conj g).toMonoidHom) :
    globalR V = ((d + 1 : ℕ) : ℕ∞) ∧
      rank (inducedAutomizer V (offenderNormalizer V g)) = d ∧
      subgroupCorank V (V ⊓ centralizer (offenderNormalizer V g : Set G)) = d + 1 ∧
      rank (V ⊓ centralizer (offenderNormalizer V g : Set G)) = rank V - (d + 1) ∧
      V ⊓ centralizer (offenderNormalizer V g : Set G) =
        V ⊓ V.map (MulAut.conj g).toMonoidHom := by
  have hineq := (lemma_E_3_28 hT (Or.inr hFF) hOff).2.1.1
  rw [hw] at hineq
  have hau := (offender_automizer_rank_le V g).trans hm
  have hal : d + 1 ≤ 1 + rank (inducedAutomizer V (offenderNormalizer V g)) := by
    have h := hr.trans hineq
    exact_mod_cast h
  have ha : rank (inducedAutomizer V (offenderNormalizer V g)) = d := by omega
  have hre : globalR V = ((d + 1 : ℕ) : ℕ∞) := by
    apply le_antisymm _ hr
    simpa only [ha, add_comm, ENat.natCast_add, ENat.natCast_one] using hineq
  have hcor : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (offenderNormalizer V g) = 1 := by
    exact_mod_cast hOff.2.symm.trans hw
  have he := fixed_eq_intersection_of_nonFF V g hFF (ha ▸ hd) hkernel hcor
  have hz := intersection_corank V g hkernel
  rw [← he, hcor, ha] at hz
  have hsum := rank_add_corank
    (show V ⊓ centralizer (offenderNormalizer V g : Set G) ≤ V from inf_le_left)
  exact ⟨hre, ha, by omega, by omega, he⟩

/-- The rank comparison at the beginning of the proof of 8.2.5, also applicable to the cocode row. The module calculations supply the rank identity. -/
theorem fixed_eq_intersection_of_ranks (V : Subgroup G) [IsElementaryAbelian 2 V]
    (g : G)
    (hkernel : offenderNormalizer V g ⊓ centralizer (V : Set G) =
      V ⊓ V.map (MulAut.conj g).toMonoidHom)
    (hranks : rank (V ⊓ centralizer (offenderNormalizer V g : Set G)) +
      subgroupCorank (V.map (MulAut.conj g).toMonoidHom) (offenderNormalizer V g) +
      rank (inducedAutomizer V (offenderNormalizer V g)) = rank V) :
    V ⊓ centralizer (offenderNormalizer V g : Set G) =
      V ⊓ V.map (MulAut.conj g).toMonoidHom := by
  have hz := intersection_corank V g hkernel
  have hu := rank_add_corank
    (show V ⊓ centralizer (offenderNormalizer V g : Set G) ≤ V from inf_le_left)
  exact (eq_of_corank_eq (intersection_le_fixed V g) inf_le_left (by omega)).symm

/-- All fixed-subgroup consequences of the table: U = C_A(V) = Z_I, relative normality in T, containment of T in its normalizer, and I ≤ C_G(U). The inputs are the rank identity and normalization of the literal actor image. -/
theorem fixed_subgroup_conclusions (V : Subgroup G) [IsElementaryAbelian 2 V]
    (T : Sylow 2 G) (g : G) (hT : HypothesisE322 V T)
    (hkernel : offenderNormalizer V g ⊓ centralizer (V : Set G) =
      V ⊓ V.map (MulAut.conj g).toMonoidHom)
    (hranks : rank (V ⊓ centralizer (offenderNormalizer V g : Set G)) +
      subgroupCorank (V.map (MulAut.conj g).toMonoidHom) (offenderNormalizer V g) +
      rank (inducedAutomizer V (offenderNormalizer V g)) = rank V)
    (himage : inducedAutomizer V T ≤
      normalizer (inducedAutomizer V (offenderNormalizer V g) : Set (Automizer V))) :
    let U := V ⊓ centralizer (offenderNormalizer V g : Set G)
    U = offenderNormalizer V g ⊓ centralizer (V : Set G) ∧
      U = V ⊓ V.map (MulAut.conj g).toMonoidHom ∧
      (U.subgroupOf T).Normal ∧
      (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      V ⊔ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (U : Set G) := by
  have he := fixed_eq_intersection_of_ranks V g hkernel hranks
  exact ⟨he.trans hkernel.symm, he,
    fixed_normal_in_sylow V _ T hT.le_sylow inf_le_right hT.normalizes himage,
    fixed_normalized_of_image_normalized V _ T inf_le_right hT.normalizes himage,
    generated_pair_centralizes_fixed V g he⟩

/-- The equality argument in 8.2.4 before excluding n > 1. The lower fixed-codimension bound is H.4.4(3); the corank is k = n from the still separate 8.2.3. -/
theorem hermitian_rank_saturation (V : Subgroup G) [IsElementaryAbelian 2 V]
    (g : G) (n : ℕ)
    (hkernel : offenderNormalizer V g ⊓ centralizer (V : Set G) =
      V ⊓ V.map (MulAut.conj g).toMonoidHom)
    (hcorank : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (offenderNormalizer V g) = n)
    (hdim : rank V = 9 * n)
    (hupper : rank (inducedAutomizer V (offenderNormalizer V g)) ≤ 4 * n)
    (hlower : 5 * n ≤ fixedCodim (automizerRepresentation V)
      (inducedAutomizer V (offenderNormalizer V g))) :
    rank (inducedAutomizer V (offenderNormalizer V g)) = 4 * n ∧
      rank (V ⊓ centralizer (offenderNormalizer V g : Set G)) = 4 * n ∧
      V ⊓ centralizer (offenderNormalizer V g : Set G) =
        V ⊓ V.map (MulAut.conj g).toMonoidHom := by
  rw [fixedCodim_inducedAutomizer V (offenderNormalizer V g) inf_le_right] at hlower
  have hz := intersection_corank V g hkernel
  rw [hcorank] at hz
  have hadd := offender_corank_add (intersection_le_fixed V g)
    (show V ⊓ centralizer (offenderNormalizer V g : Set G) ≤ V from inf_le_left)
  have hsum := rank_add_corank
    (show V ⊓ centralizer (offenderNormalizer V g : Set G) ≤ V from inf_le_left)
  refine ⟨by omega, by omega, ?_⟩
  exact (eq_of_corank_eq (intersection_le_fixed V g) inf_le_left (by omega)).symm

/-- Application of the fixed-subgroup theorem to the actual code offenders. With d = 5 or 6 this gives respectively (r, m(Abar), m(U)) = (6, 5, 4) or (7, 6, 4). The actual K_Q/K_S identifications and their image normality are supplied by H.16.5, not by a family label. -/
theorem code_offender_conclusions (V : Subgroup G) [IsElementaryAbelian 2 V]
    (T : Sylow 2 G) (g : G) (hT : HypothesisE322 V T)
    (hFF : ¬ IsFFModule (automizerRepresentation V)) (hOff : IsWOffenderAt V T g)
    (hw : globalW V T = 1) (d : ℕ) (hd : 0 < d)
    (hr : ((d + 1 : ℕ) : ℕ∞) ≤ globalR V)
    (hm : primeRank 2 (Automizer V) ≤ d) (hdim : rank V = d + 5)
    (hkernel : offenderNormalizer V g ⊓ centralizer (V : Set G) =
      V ⊓ V.map (MulAut.conj g).toMonoidHom)
    (himage : inducedAutomizer V T ≤
      normalizer (inducedAutomizer V (offenderNormalizer V g) : Set (Automizer V))) :
    let A := offenderNormalizer V g
    let U := V ⊓ centralizer (A : Set G)
    globalR V = ((d + 1 : ℕ) : ℕ∞) ∧ rank (inducedAutomizer V A) = d ∧
      rank U = 4 ∧ U = A ⊓ centralizer (V : Set G) ∧
      U = V ⊓ V.map (MulAut.conj g).toMonoidHom ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      V ⊔ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (U : Set G) := by
  obtain ⟨hre, ha, _, hu, he⟩ := code_row_parameters V T g hT hFF hOff hw d hd hr hm hkernel
  have hu4 : rank (V ⊓ centralizer (offenderNormalizer V g : Set G)) = 4 := by
    rw [hdim] at hu
    omega
  have hcor : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (offenderNormalizer V g) = 1 := by exact_mod_cast hOff.2.symm.trans hw
  have hsum : rank (V ⊓ centralizer (offenderNormalizer V g : Set G)) +
      subgroupCorank (V.map (MulAut.conj g).toMonoidHom) (offenderNormalizer V g) +
      rank (inducedAutomizer V (offenderNormalizer V g)) = rank V := by
    rw [hu4, hcor, ha, hdim]
    omega
  exact ⟨hre, ha, hu4, fixed_subgroup_conclusions V T g hT hkernel hsum himage⟩

/-- Application to the Hermitian offender after k = w = n. E.3.28 proves the rank threshold needed by the explicit H.4.4(3) input, and then gives m(Abar) = m(U) = 4n, U = Z_I and r ≤ 5n. The n = 1 exclusion and L3(4) identification remain separate source obligations. -/
theorem hermitian_offender_parameters (V : Subgroup G) [IsElementaryAbelian 2 V]
    (T : Sylow 2 G) (g : G) (n : ℕ) (hn : 0 < n)
    (hT : HypothesisE322 V T) (hOff : IsWOffenderAt V T g)
    (hw : globalW V T = n) (hr : ((4 * n : ℕ) : ℕ∞) ≤ globalR V)
    (hm : primeRank 2 (Automizer V) ≤ 4 * n) (hdim : rank V = 9 * n)
    (hkernel : offenderNormalizer V g ⊓ centralizer (V : Set G) =
      V ⊓ V.map (MulAut.conj g).toMonoidHom)
    (hfixed : ∀ B : Subgroup (Automizer V), IsElementaryTwo B →
      3 * n ≤ rank B → 5 * n ≤ fixedCodim (automizerRepresentation V) B) :
    rank (inducedAutomizer V (offenderNormalizer V g)) = 4 * n ∧
      rank (V ⊓ centralizer (offenderNormalizer V g : Set G)) = 4 * n ∧
      V ⊓ centralizer (offenderNormalizer V g : Set G) =
        V ⊓ V.map (MulAut.conj g).toMonoidHom ∧
      globalR V ≤ ((5 * n : ℕ) : ℕ∞) := by
  have hwpos : 0 < globalW V T := by rw [hw]; exact_mod_cast hn
  have hineq := (lemma_E_3_28 hT (Or.inl hwpos) hOff).2.1.1
  rw [hw] at hineq
  have hnat : 4 * n ≤ n + rank (inducedAutomizer V (offenderNormalizer V g)) := by
    exact_mod_cast hr.trans hineq
  have ha3 : 3 * n ≤ rank (inducedAutomizer V (offenderNormalizer V g)) := by omega
  have hA : IsElementaryTwo (inducedAutomizer V (offenderNormalizer V g)) := by
    refine ⟨?_, offender_inducedAutomizer_elementary V g⟩
    intro hbot
    rw [hbot, Representation.BinaryOffender.rank_bot] at ha3
    omega
  have hcor : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (offenderNormalizer V g) = n := by exact_mod_cast hOff.2.symm.trans hw
  obtain ⟨ha, hu, he⟩ := hermitian_rank_saturation V g n hkernel hcor hdim
    ((offender_automizer_rank_le V g).trans hm) (hfixed _ hA ha3)
  refine ⟨ha, hu, he, ?_⟩
  rw [ha] at hineq
  have hadd : n + 4 * n = 5 * n := by omega
  simpa only [← ENat.natCast_add, hadd] using hineq

end CFSG.Quasithin.Chapter8.Section02.Offenders
