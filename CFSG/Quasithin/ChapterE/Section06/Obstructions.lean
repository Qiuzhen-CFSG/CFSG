module

public import CFSG.Quasithin.ChapterE.Section06.Basic
public import CFSG.Quasithin.ChapterE.Section03.Parameters.AutomizerFF

/-!
# Selecting the centralizer obstructions

The minimum defining `r` is attained whenever it is finite. Below the module
parameter `m`, its witnessing subspace is nonidentity, and the local centralizer
has odd induced action: otherwise Cauchy's theorem produces an involution whose
fixed codimension is both at least `m` and below `m`. The kernel of the actual
action therefore contains the odd-index residual. This proves that a failure
of the desired lower bound gives a member of the genuine family Γ.

A second argument enlarges a subspace maximally while preserving its escaping
centralizer. If its local centralizer is already `C_M(V)`, the nontrivial-action
conclusion of E.6.11(2) rules out corank greater than one. We prove this
implication with that structural input explicit, for later assembly of E.6.12.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), observations after E.6.4, p.245, and the proof of
E.6.12, p.250 (PDF pp.256 and 261). The action and corank bridges are from E.3.
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterE.Section06
variable {G : Type*} [Group G] [Finite G] {V M U : Subgroup G}

/-- The corank of the zero subspace is the binary dimension of V. -/
theorem corank_bot (V : Subgroup G) [IsElementaryAbelian 2 V] :
    subgroupCorank V ⊥ = Module.finrank (ZMod 2) (Additive V) := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
  change Nat.card V = _ at hc
  simp only [Nat.card_zmod] at hc
  simp only [subgroupCorank, Subgroup.relIndex_bot_left, hc, Nat.log_pow (by decide : 1 < 2)]

/-- The dimension bound on m excludes the zero subspace below m. -/
theorem nontrivial_of_corank_lt_localM [IsElementaryAbelian 2 V]
    (h : subgroupCorank V U < localM V) : U ≠ ⊥ := by
  rintro rfl
  rw [corank_bot] at h
  exact (not_lt_of_ge (moduleM_le_dimension (automizerRepresentation V))) h

omit [Finite G] in
/-- A finite global parameter is attained by an actual escaping centralizer. -/
theorem globalR_attained (h : globalR V ≠ ⊤) :
    ∃ U : Subgroup G, U ≤ V ∧ ¬ centralizer (U : Set G) ≤ normalizer (V : Set G) ∧
      (subgroupCorank V U : ℕ∞) = globalR V := by
  have hex : ∃ U : Subgroup G,
      U ≤ V ∧ ¬ centralizer (U : Set G) ≤ normalizer (V : Set G) := by
    by_contra! hn
    exact h ((globalR_eq_top_iff V).mpr hn)
  let W := {U : Subgroup G // U ≤ V ∧ ¬ centralizer (U : Set G) ≤ normalizer (V : Set G)}
  have : Nonempty W := by obtain ⟨U, hU⟩ := hex; exact ⟨U, hU⟩
  obtain ⟨U, hU⟩ := ENat.exists_eq_iInf (fun U : W => (subgroupCorank V U.1 : ℕ∞))
  exact ⟨U.1, U.2.1, U.2.2, by simpa only [W, iInf_subtype, globalR] using hU⟩

/-- An escaping hyperplane, together with N_G(V) ≤ M, forces r = 1. -/
theorem globalR_eq_one_of_hyperplane (hNV : normalizer (V : Set G) ≤ M)
    (hUV : U ≤ V) (hc : subgroupCorank V U = 1) (he : ¬ centralizer (U : Set G) ≤ M) :
    globalR V = 1 := by
  apply le_antisymm _ (one_le_globalR V)
  simpa only [hc, Nat.cast_one] using
    globalR_le_corank hUV (fun hn => he (hn.trans hNV))

omit [Finite G] in
/-- Equality of the two endpoint centralizers persists along the subspace interval. -/
theorem localCentralizer_eq_of_between {W : Subgroup G} (hUW : U ≤ W) (hWV : W ≤ V)
    (h : M ⊓ centralizer (U : Set G) = M ⊓ centralizer (V : Set G)) :
    M ⊓ centralizer (W : Set G) = M ⊓ centralizer (V : Set G) := by
  apply le_antisymm
  · exact (inf_le_inf_left M (Subgroup.centralizer_le hUW)).trans h.le
  · exact inf_le_inf_left M (Subgroup.centralizer_le hWV)

/-- Enlarge an escaping subspace to one maximal under inclusion. -/
theorem exists_maximal_escape (hUV : U ≤ V) (he : ¬ centralizer (U : Set G) ≤ M) :
    ∃ W : Subgroup G, U ≤ W ∧ W ≤ V ∧ ¬ centralizer (W : Set G) ≤ M ∧
      ∀ X : Subgroup G, W < X → X ≤ V → centralizer (X : Set G) ≤ M := by
  obtain ⟨W, hUW, hW⟩ := Finite.exists_le_maximal
    (p := fun W : Subgroup G => W ≤ V ∧ ¬ centralizer (W : Set G) ≤ M) ⟨hUV, he⟩
  refine ⟨W, hUW, hW.1.1, hW.1.2, ?_⟩
  intro X hWX hXV
  by_contra hn
  exact hWX.not_ge (hW.2 ⟨hXV, hn⟩ hWX.le)

omit [Finite G] in
/-- Equality C_M(U) = C_M(V) implies the residual condition defining Γ. -/
theorem oddCentralizerCondition_of_eq
    (h : M ⊓ centralizer (U : Set G) = M ⊓ centralizer (V : Set G)) :
    oddCentralizerCondition M V U := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := hx
  exact h ▸ y.property

/-- Enlarging the subspace decreases its binary corank. -/
theorem subgroupCorank_antitone {W : Subgroup G} (hUW : U ≤ W) :
    subgroupCorank V W ≤ subgroupCorank V U := by
  apply Nat.log_mono_right
  apply Subgroup.relIndex_le_of_le_left hUW
  intro hz
  have hdvd := U.relIndex_dvd_card V
  rw [hz, zero_dvd_iff] at hdvd
  exact Nat.card_pos.ne' hdvd

/-- Below m, an induced action fixing U has odd order: an involution would move at least m dimensions. -/
theorem odd_inducedAutomizer_of_corank_lt_localM [IsElementaryAbelian 2 V]
    {C : Subgroup G} (hCN : C ≤ normalizer (V : Set G))
    (hCU : C ≤ centralizer (U : Set G)) (hUV : U ≤ V)
    (hsmall : subgroupCorank V U < localM V) :
    Odd (Nat.card (inducedAutomizer V C)) := by
  open Representation.BinaryOffender in
  have hdim : fixedCodim (automizerRepresentation V) (inducedAutomizer V C) ≤
      subgroupCorank V U := by
    rw [fixedCodim_inducedAutomizer V C hCN]
    exact subgroupCorank_antitone (le_inf hUV (le_centralizer_iff.mpr hCU))
  by_contra hn
  have he : Even (Nat.card (inducedAutomizer V C)) := Nat.not_odd_iff_even.mp hn
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card'
    (G := inducedAutomizer V C) 2 (even_iff_two_dvd.mp he)
  have ht' : orderOf (t : Automizer V) = 2 := (Subgroup.orderOf_coe t).trans ht
  have hm := (moduleM_le_involution (automizerRepresentation V) ht').trans
    (fixedCodim_mono (automizerRepresentation V) (Subgroup.zpowers_le.mpr t.property))
  exact (not_lt_of_ge (hm.trans hdim)) hsmall

omit [Finite G] in
/-- The actual odd action image kills O^{2′}(C_M(U)); its kernel is the relative centralizer of V. -/
theorem oddCentralizerCondition_of_odd_image
    (hCN : M ⊓ centralizer (U : Set G) ≤ normalizer (V : Set G))
    (hodd : Odd (Nat.card (inducedAutomizer V (M ⊓ centralizer (U : Set G))))) :
    oddCentralizerCondition M V U := by
  let C := M ⊓ centralizer (U : Set G)
  let I := inducedAutomizer V C
  let f : C →* I :=
    { toFun := fun c => ⟨V.normalizerMonoidHom.rangeRestrict ⟨c, hCN c.property⟩,
        ⟨⟨c, hCN c.property⟩, c.property, rfl⟩⟩
      map_one' := by apply Subtype.ext; exact map_one V.normalizerMonoidHom.rangeRestrict
      map_mul' := by
        intro a b
        apply Subtype.ext
        exact map_mul V.normalizerMonoidHom.rangeRestrict
          ⟨a, hCN a.property⟩ ⟨b, hCN b.property⟩ }
  have hr : primeToResidual 2 C ≤ f.ker :=
    primeToResidual_le_ker f (Nat.coprime_two_left.mpr hodd)
  rintro x ⟨c, hc, rfl⟩
  refine ⟨c.property.1, ?_⟩
  have hf := MonoidHom.mem_ker.mp (hr hc)
  have hn : (⟨c, hCN c.property⟩ : normalizer (V : Set G)) ∈ V.normalizerMonoidHom.ker := by
    change V.normalizerMonoidHom ⟨c, hCN c.property⟩ = 1
    exact congrArg (fun a : I => ((a : Automizer V) : MulAut V)) hf
  rwa [Subgroup.normalizerMonoidHom_ker] at hn

/-- The local residual observation following Definition E.6.4. -/
theorem HypothesisE61.oddCentralizerCondition_of_small
    {K : CFSG.Quasithin.GroupClass} {T : Sylow 2 G}
    (h : HypothesisE61 K T M V) [IsElementaryAbelian 2 V]
    (hUV : U ≤ V) (hsmall : subgroupCorank V U < localM V) :
    oddCentralizerCondition M V U := by
  have hCN := h.localCentralizer_le_normalizer (nontrivial_of_corank_lt_localM hsmall) hUV
  exact oddCentralizerCondition_of_odd_image hCN
    (odd_inducedAutomizer_of_corank_lt_localM hCN inf_le_right hUV hsmall)

/-- If r < m, the minimum defining r is attained inside the source obstruction family Γ. -/
theorem HypothesisE61.exists_minimal_obstruction
    {K : CFSG.Quasithin.GroupClass} {T : Sylow 2 G}
    (h : HypothesisE61 K T M V) [IsElementaryAbelian 2 V]
    (hsmall : globalR V < (localM V : ℕ∞)) :
    ∃ U ∈ obstructionFamily M V, (subgroupCorank V U : ℕ∞) = globalR V := by
  obtain ⟨U, hUV, he, hcor⟩ := globalR_attained (ne_top_of_lt hsmall)
  have hs : subgroupCorank V U < localM V := by
    apply ENat.natCast_lt_natCast.mp
    rwa [hcor]
  have hne := nontrivial_of_corank_lt_localM hs
  exact ⟨U, ⟨hUV, hne, fun hc => he ((h.centralizer_le_iff hne hUV).mp hc),
    h.oddCentralizerCondition_of_small hUV hs⟩, hcor⟩

/-- The implication from the nontrivial-action conclusion of E.6.11(2) to E.6.12.
The action premise remains explicit here; the full source theorem must supply
it from the structural analysis of maximal members of Γ. -/
theorem HypothesisE61.hyperplane_escape_of_maximal_action
    {K : CFSG.Quasithin.GroupClass} {T : Sylow 2 G}
    (h : HypothesisE61 K T M V)
    (hact : ∀ W ∈ obstructionFamily M V,
      (∀ X : Subgroup G, W < X → X ≤ V → centralizer (X : Set G) ≤ M) →
      1 < subgroupCorank V W →
      ∃ x ∈ M ⊓ centralizer (W : Set G), x ∉ centralizer (V : Set G))
    (hU : U ≠ ⊥) (hUV : U ≤ V)
    (hC : M ⊓ centralizer (U : Set G) = M ⊓ centralizer (V : Set G))
    (he : ¬ centralizer (U : Set G) ≤ M) :
    ∃ W : Subgroup G, U ≤ W ∧ W ≤ V ∧ subgroupCorank V W = 1 ∧
      ¬ centralizer (W : Set G) ≤ M ∧ globalR V = 1 := by
  obtain ⟨W, hUW, hWV, hW, hmax⟩ := exists_maximal_escape hUV he
  have hWne : W ≠ ⊥ := fun hb => hU (le_bot_iff.mp (hb ▸ hUW))
  have hCW := localCentralizer_eq_of_between hUW hWV hC
  have hWG : W ∈ obstructionFamily M V :=
    ⟨hWV, hWne, hW, oddCentralizerCondition_of_eq hCW⟩
  have hpos : 1 ≤ subgroupCorank V W := by
    have hbound := (one_le_globalR V).trans
      (globalR_le_corank hWV (fun hc => hW (hc.trans h.normalizer_le)))
    exact_mod_cast hbound
  have hnot : ¬ 1 < subgroupCorank V W := by
    intro hn
    obtain ⟨x, hx, hxn⟩ := hact W hWG hmax hn
    exact hxn ((hCW ▸ hx).2)
  have hcor : subgroupCorank V W = 1 := by omega
  exact ⟨W, hUW, hWV, hcor, hW, globalR_eq_one_of_hyperplane h.normalizer_le hWV hcor hW⟩

end CFSG.Quasithin.ChapterE.Section06
