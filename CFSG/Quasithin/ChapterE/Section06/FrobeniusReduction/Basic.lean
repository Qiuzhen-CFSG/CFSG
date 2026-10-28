module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.Defs

/-!
# Fixed-space elimination and terminal consequences in E.6.25

We form the normal closure in N_G(V) before mapping it to G and to the
actual automizer. If its fixed subgroup in V were nontrivial, E.6.1's
unique maximal two-local would contain its centralizer, hence C_G(U).
This contradicts U ∈ Γ. This is the first paragraph of the proof of E.6.25.

Separately, an odd automizer kills the image of the Sylow two-subgroup,
giving T = C_T(V). Counting the actual quotient gives |U| = 2 when V has
dimension three and U has corank two. The normal-closure decomposition,
its Frobenius identification, and the two-factor exclusion remain needed
before these deductions establish E.6.24–25.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.255–256 (PDF pp.266–267).
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction

variable {G : Type*} [Group G]

/-- The normal closure of X inside N_G(V), mapped into G. -/
def normalClosureLift (V X : Subgroup G) : Subgroup G :=
  (normalClosure (X.subgroupOf (normalizer (V : Set G)) : Set (normalizer (V : Set G)))).map
    (normalizer (V : Set G)).subtype

theorem normalClosureLift_le (V X : Subgroup G) :
    normalClosureLift V X ≤ normalizer (V : Set G) := map_subtype_le _

theorem le_normalClosureLift {V X : Subgroup G}
    (hX : X ≤ normalizer (V : Set G)) : X ≤ normalClosureLift V X := by
  intro x hx
  exact ⟨⟨x, hX hx⟩, le_normalClosure hx, rfl⟩

theorem normalizer_le_normalizer_normalClosureLift (V X : Subgroup G) :
    normalizer (V : Set G) ≤ normalizer (normalClosureLift V X : Set G) := by
  apply le_normalizer_iff.mpr
  rintro g hg x ⟨y, hy, rfl⟩
  exact ⟨(⟨g, hg⟩ : normalizer (V : Set G)) * y * ⟨g, hg⟩⁻¹,
    normalClosure_normal.conj_mem y hy ⟨g, hg⟩, rfl⟩

theorem inducedAutomizer_normalClosureLift (V X : Subgroup G) :
    inducedAutomizer V (normalClosureLift V X) =
      normalClosure (inducedAutomizer V X : Set (Automizer V)) := by
  unfold inducedAutomizer normalClosureLift
  change (((normalClosure (X.subgroupOf (normalizer (V : Set G)) :
    Set (normalizer (V : Set G)))).map (normalizer (V : Set G)).subtype).comap
      (normalizer (V : Set G)).subtype).map V.normalizerMonoidHom.rangeRestrict = _
  rw [Subgroup.comap_map_eq_self_of_injective (normalizer (V : Set G)).subtype_injective]
  rw [Subgroup.map_normalClosure _ _ V.normalizerMonoidHom.rangeRestrict_surjective]
  rfl

variable [Finite G] {K : GroupClass} {T : Sylow 2 G} {M V U X : Subgroup G}

theorem fixedSubgroup_eq_bot (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) {Y : Subgroup G}
    (hXY : X ≤ Y) (hfixed : V ⊓ centralizer (X : Set G) = U)
    (hNY : normalizer (V : Set G) ≤ normalizer (Y : Set G)) :
    V ⊓ centralizer (Y : Set G) = ⊥ := by
  let F := V ⊓ centralizer (Y : Set G)
  have hFV : F ≤ V := inf_le_left
  have hFU : F ≤ U := by
    rw [← hfixed]
    exact inf_le_inf_left V (Subgroup.centralizer_le hXY)
  have hNF : normalizer (V : Set G) ≤ normalizer (F : Set G) :=
    (le_inf le_rfl (hNY.trans (Subgroup.normalizer_le_normalizer_centralizer Y))).trans
      inf_normalizer_le_normalizer_inf
  by_contra hF
  let _ := h.elementary
  have hFtwo : IsPGroup 2 F :=
    (IsElementaryAbelian.isPGroup 2 V).of_injective (inclusion hFV) (inclusion_injective hFV)
  have hNM : normalizer (F : Set G) ≤ M :=
    normalizer_le_of_unique_maximalTwoLocal h.unique hFtwo hF
      ((inf_le_left.trans inf_le_right).trans hNF)
  exact hU.2.2.1 ((Subgroup.centralizer_le hFU).trans
    ((centralizer_le_normalizer _).trans hNM))

theorem normalClosure_fixedSubgroup_eq_bot (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) (hX : X ≤ normalizer (V : Set G))
    (hfixed : V ⊓ centralizer (X : Set G) = U) :
    V ⊓ centralizer (normalClosureLift V X : Set G) = ⊥ :=
  fixedSubgroup_eq_bot h hU (le_normalClosureLift hX) hfixed
    (normalizer_le_normalizer_normalClosureLift V X)

theorem sylow_eq_centralizer_of_odd_automizer (h : HypothesisE61 K T M V)
    (hodd : Odd (Nat.card (Automizer V))) :
    (T : Subgroup G) = sylowCentralizer (T : Subgroup G) V := by
  apply (inf_eq_left.mpr ?_).symm
  intro t ht
  let f : T →* Automizer V := V.normalizerMonoidHom.rangeRestrict.comp
    (inclusion h.sylow_le_normalizer)
  obtain ⟨k, hk⟩ := T.isPGroup'.exists_pow_pow_eq_one (⟨t, ht⟩ : T)
  have hp : f ⟨t, ht⟩ ^ 2 ^ k = 1 := by
    simpa only [map_pow, map_one] using congrArg f hk
  have hone : f ⟨t, ht⟩ = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (hodd.coprime_two_right.pow_right k)
      (orderOf_dvd_natCard _) (orderOf_dvd_iff_pow_eq_one.mpr hp))
  have hker : (⟨t, h.sylow_le_normalizer ht⟩ : normalizer (V : Set G)) ∈
      V.normalizerMonoidHom.ker := by
    change V.normalizerMonoidHom ⟨t, h.sylow_le_normalizer ht⟩ = 1
    exact congrArg (fun a : Automizer V => (a : MulAut V)) hone
  rwa [Subgroup.normalizerMonoidHom_ker] at hker

theorem card_eq_two_of_dimension_three_corank_two [IsElementaryAbelian 2 V]
    (hUV : U ≤ V) (hdim : Module.finrank (ZMod 2) (Additive V) = 3)
    (hcor : subgroupCorank V U = 2) : Nat.card U = 2 := by
  have hidx : (U.subgroupOf V).index = 4 := by
    change U.relIndex V = 4
    rw [V.relIndex_eq_two_pow_quotient_finrank U,
      ← subgroupCorank_eq_quotient_finrank, hcor]
    decide
  have hcard : Nat.card V = 8 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    change Nat.card V = _ at hc
    norm_num only [Nat.card_zmod, hdim] at hc
    exact hc
  have hUcard : Nat.card (U.subgroupOf V) = Nat.card U :=
    Nat.card_congr (subgroupOfEquivOfLe hUV).toEquiv
  have hc := (U.subgroupOf V).card_mul_index
  rw [hUcard, hidx, hcard] at hc
  omega

/-- The fixed space of the actual automizer normal closure is zero. -/
theorem normalClosure_fixedSpace_eq_bot (h : HypothesisE61 K T M V)
    [IsElementaryAbelian 2 V] (hU : U ∈ obstructionFamily M V)
    (hX : X ≤ normalizer (V : Set G))
    (hfixed : V ⊓ centralizer (X : Set G) = U) :
    Representation.BinaryOffender.fixedSpace (automizerRepresentation V)
      (normalClosure (inducedAutomizer V X : Set (Automizer V))) = ⊥ := by
  rw [← inducedAutomizer_normalClosureLift V X]
  apply bot_unique
  intro v hv
  have hvC := (mem_fixedSpace_inducedAutomizer V (normalClosureLift V X)
    (normalClosureLift_le V X) v).mp hv
  have hvF : (v.toMul : G) ∈ V ⊓ centralizer (normalClosureLift V X : Set G) :=
    ⟨v.toMul.property, hvC⟩
  rw [normalClosure_fixedSubgroup_eq_bot h hU hX hfixed, mem_bot] at hvF
  change v = 0
  exact congrArg Additive.ofMul (Subtype.ext hvF)

/-- The ambient cyclic subgroup cannot be normalized by all of N_G(V). -/
theorem not_normalized_cyclic_section (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hfixed : V ⊓ centralizer (X : Set G) = U) :
    ¬ normalizer (V : Set G) ≤ normalizer (X : Set G) := by
  intro hn
  have hzero := fixedSubgroup_eq_bot h hU (X := X) le_rfl hfixed hn
  exact hU.2.1 (hfixed.symm.trans hzero)

/-- In particular the cyclic action image cannot be normal in the automizer.
This excludes the single-factor cyclic alternative without assuming that
the chosen lift X is normal in N_G(V). -/
theorem not_normal_inducedAutomizer (h : HypothesisE61 K T M V)
    [IsElementaryAbelian 2 V] (hU : U ∈ obstructionFamily M V)
    (hX : X ≤ normalizer (V : Set G))
    (hfixed : V ⊓ centralizer (X : Set G) = U) :
    ¬ (inducedAutomizer V X).Normal := by
  intro hn
  let _ := hn
  have hf := normalClosure_fixedSpace_eq_bot h hU hX hfixed
  rw [normalClosure_eq_self] at hf
  obtain ⟨u, hu, hune⟩ := U.bot_or_exists_ne_one.resolve_left hU.2.1
  let v : Additive V := Additive.ofMul ⟨u, hU.1 hu⟩
  have huC : u ∈ centralizer (X : Set G) := (hfixed.symm ▸ hu).2
  have hv := (mem_fixedSpace_inducedAutomizer V X hX v).mpr huC
  rw [hf, Submodule.mem_bot] at hv
  exact hune (congrArg (fun w : Additive V => (w.toMul : G)) hv)

/-- In any supplied E.6.24 decomposition the summands fill V, since the
fixed summand is zero by the escaping-centralizer argument. -/
theorem decomposition_spans (h : HypothesisE61 K T M V)
    [IsElementaryAbelian 2 V] (hU : U ∈ obstructionFamily M V)
    (hX : X ≤ normalizer (V : Set G))
    (hfixed : V ⊓ centralizer (X : Set G) = U)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X)) :
    (⨆ i, D.summand i) = ⊤ := by
  have hs := D.split.sup_eq_top
  rw [normalClosure_fixedSpace_eq_bot h hU hX hfixed, bot_sup_eq, D.moved_eq] at hs
  exact hs

/-- The cyclic alternative in E.6.24 requires more than one factor. -/
theorem cyclic_decomposition_size_ne_one (h : HypothesisE61 K T M V)
    [IsElementaryAbelian 2 V] (hU : U ∈ obstructionFamily M V)
    (hX : X ≤ normalizer (V : Set G))
    (hfixed : V ⊓ centralizer (X : Set G) = U)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (hcyclic : inducedAutomizer V X = D.factor D.distinguished) : D.size ≠ 1 := by
  intro hsize
  have : Subsingleton (Fin D.size) := by rw [hsize]; infer_instance
  have hall : (⨆ i, D.factor i) = inducedAutomizer V X := by
    apply le_antisymm
    · apply iSup_le
      intro i
      rw [Subsingleton.elim i D.distinguished, ← hcyclic]
    · exact hcyclic.le.trans (le_iSup D.factor D.distinguished)
  have heq := D.group_eq.symm.trans hall
  apply not_normal_inducedAutomizer h hU hX hfixed
  rw [← heq]
  infer_instance

/-- The last two source conclusions follow once the exceptional identification
and its module dimensions have been established. This is a conditional
assembly lemma, not the Frobenius identification itself. -/
theorem card_and_sylow_of_frobenius_identification (h : HypothesisE61 K T M V)
    [IsElementaryAbelian 2 V] (hU : U ≤ V)
    (e : Automizer V ≃* Frobenius21.Model)
    (hdim : Module.finrank (ZMod 2) (Additive V) = 3)
    (hcor : subgroupCorank V U = 2) :
    Nat.card U = 2 ∧ (T : Subgroup G) = sylowCentralizer (T : Subgroup G) V := by
  have hc : Nat.card (Automizer V) = 21 :=
    (Nat.card_congr e.toEquiv).trans Frobenius21.card_model
  exact ⟨card_eq_two_of_dimension_three_corank_two hU hdim hcor,
    sylow_eq_centralizer_of_odd_automizer h (by rw [hc]; decide)⟩

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
