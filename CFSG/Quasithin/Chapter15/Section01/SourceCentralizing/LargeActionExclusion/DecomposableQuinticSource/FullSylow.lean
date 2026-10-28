module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableQuinticSource.FullCubic
public import Theory.GroupTheory.PResidual.CyclicThree

/-!
# The original marked Sylow subgroup for the full partner

The surviving cubic action has Sylow two-subgroups of order at most two.
The original support exchange gives its nontrivial element, so an element
fixing the first Thompson plane fixes all of E. Its pointwise centralizer
in T is therefore normal in T.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The original marked Sylow subgroup is the kernel of the full E action. -/
theorem PreparedChosenModule.decomposable_five_full_partner_marked_sylow_normal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      localModule T Mc = thompsonFixed T V →
      let E := thompsonFixed T V
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      (T : Subgroup G)⊓centralizer (Z₁ : Set G)=
        (T : Subgroup G)⊓centralizer (E : Set G) ∧
      (((T : Subgroup G)⊓centralizer (Z₁ : Set G)).subgroupOf (T : Subgroup G)).Normal := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hUcEq
  let E := thompsonFixed T V
  let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
  let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
  obtain ⟨hn,hcore,he,hcard,hquot⟩ := h.decomposable_five_full_partner_three_core_card_three
    hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hq hfive hUcEq
  let D := internalActionImage Mc E hn
  let R := pCore 3 D
  let : IsElementaryAbelian 3 R := he
  let : IsCyclic R := isCyclic_of_prime_card hcard
  have hres : pResidual 2 D ≤ R := (pResidual_le_iff_isPGroup_quotient 2 R).mpr hquot
  let : IsCyclic (pResidual 2 D) := isCyclic_of_le hres
  have hthree : IsPGroup 3 (pResidual 2 D) := (IsElementaryAbelian.isPGroup 3 R).to_le hres
  have hMcC : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  let f : Mc →* D := (actionHom Mc E hn).rangeRestrict
  let P : Sylow 2 D := (T.subtype hTMc).mapSurjective
    (actionHom Mc E hn).rangeRestrict_surjective
  have hPcard : Nat.card P ≤ 2 := P.card_le_two_of_cyclic_three_residual hcore hthree
  have hmem (t : G) (ht : t ∈ (T : Subgroup G)) : f ⟨t,hTMc ht⟩ ∈ (P : Subgroup D) := by
    change f ⟨t,hTMc ht⟩ ∈ (T.subtype hTMc : Subgroup Mc).map f
    exact mem_map_of_mem f ht
  obtain ⟨t,ht,hout⟩ : ∃ t ∈ (T : Subgroup G),
      t ∉ normalizer (plane V (c.ambientFactor d s.first).space : Set G) := by
    by_contra! hall
    have hh := relIndex_eq_one.mpr (le_inf le_rfl hall)
    rw [s.stabilizer_index] at hh
    contradiction
  have hex : Z₁.map (MulAut.conj t).toMonoidHom = Z₂ := (s.thompson_exchanges t ht hout).1
  have htC : t ∉ centralizer (Z₁ : Set G) := by
    intro hc
    obtain ⟨z,hzne⟩ := ne_bot_iff_exists_ne_one.mp
      ((one_lt_card_iff_ne_bot Z₁).mp (by rw [s.thompson_card s.first]; decide))
    have htz : t*(z:G)*t⁻¹ = z := by rw [←hc z z.property,mul_inv_cancel_right]
    have hz₂ : (z:G) ∈ Z₂ := htz ▸ (hex ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom z.property)
    exact hzne (Subtype.ext (mem_bot.mp (s.thompson_disjoint.le ⟨z.property,hz₂⟩)))
  let a : P := ⟨f ⟨t,hTMc ht⟩,hmem t ht⟩
  have ha : a ≠ 1 := by
    intro ha
    have hk : (⟨t,hTMc ht⟩ : Mc) ∈ (actionHom Mc E hn).ker :=
      congrArg Subtype.val (congrArg Subtype.val ha)
    rw [actionHom_ker] at hk
    exact htC ((centralizer_le (show Z₁ ≤ E from inf_le_right)) hk)
  have hPtwo : Nat.card P = 2 := by
    have hp := Nat.card_pos (α := P)
    have hne : Nat.card P ≠ 1 := by
      intro hh
      let : Subsingleton P := (Nat.card_eq_one_iff_unique.mp hh).1
      exact ha (Subsingleton.elim _ _)
    omega
  obtain ⟨a₀,ha₀,hunique⟩ := (Nat.card_eq_two_iff' (1:P)).mp hPtwo
  have heq : (T : Subgroup G) ⊓ centralizer (Z₁ : Set G) =
      (T : Subgroup G) ⊓ centralizer (E : Set G) := by
    apply le_antisymm
    · intro x hx
      refine ⟨hx.1,?_⟩
      let b : P := ⟨f ⟨x,hTMc hx.1⟩,hmem x hx.1⟩
      have hb : b = 1 := by
        by_contra hb
        have hba : b = a := (hunique b hb).trans (hunique a ha).symm
        have hmap : f ⟨x,hTMc hx.1⟩ = f ⟨t,hTMc ht⟩ := congrArg Subtype.val hba
        apply htC
        intro z hz
        have hzE : z ∈ E := (show Z₁ ≤ E from inf_le_right) hz
        have heval := congrArg (fun q : D => ((q:MulAut E) ⟨z,hzE⟩ : G)) hmap
        change x*z*x⁻¹ = t*z*t⁻¹ at heval
        have hxz : x*z*x⁻¹ = z := by rw [←hx.2 z hz,mul_inv_cancel_right]
        exact (mul_inv_eq_iff_eq_mul.mp (heval.symm.trans hxz)).symm
      have hk : (⟨x,hTMc hx.1⟩ : Mc) ∈ (actionHom Mc E hn).ker :=
        congrArg Subtype.val (congrArg Subtype.val hb)
      rwa [actionHom_ker] at hk
    · exact inf_le_inf_left _ (centralizer_le (show Z₁ ≤ E from inf_le_right))
  refine ⟨heq,?_⟩
  rw [heq]
  exact normal_subgroupOf_of_le_normalizer
    ((le_inf (T : Subgroup G).le_normalizer
      ((hTMc.trans hn).trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf)

end CFSG.Quasithin.Chapter15.Section01
