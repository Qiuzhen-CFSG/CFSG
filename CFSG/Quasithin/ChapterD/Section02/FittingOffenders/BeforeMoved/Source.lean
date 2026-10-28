module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.BeforeMoved.Restriction
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.BeforeMoved.Kernel

/-!
# The old noncyclic actor modulo the Fitting subgroup

The actual PA action supplies two or three support planes on [V,O₃].
Rigidity in the original faithful representation makes these factors
canonical, so ambient conjugation permutes them. The normal closure of the
old actor centralizes the complementary odd cores, and its fourth powers
centralize O₃. Self-centralization of F therefore puts these fourth powers
in F. Its literal image in G/F is a normal two-group.

This supplies the noncyclic per-actor input to the initial reduction of
Aschbacher–Smith 15.1.2, printed p.1084. It retains the original minimum
actor and makes no assertion about the ranks of the other starred actors.
-/

public section
namespace CFSG.Quasithin.ChapterD.BeforeMoved
open Subgroup Representation.BinaryOffender FittingConfigurations Theory.GroupTheory
open ElementaryCore.SupportExclusion
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

omit [FiniteDimensional (ZMod 2) V] in
private theorem movedModule_commutator_map (P : Subgroup G) [P.Normal]
    (hodd : Odd (Nat.card P)) (D : Subgroup G) (hDP : D ≤ P) :
    (subspaceCommutator (movedModule ρ P).toRepresentation ⊤ D).map
        (movedModule ρ P).toSubmodule.subtype = subspaceCommutator ρ ⊤ D := by
  simpa only [fixedSpace_bot] using movedModule_fixed_commutator_map ρ P hodd ⊥ D hDP

private theorem moved_factors_permuted (hf : Function.Injective ρ)
    (P : Subgroup G) [P.Normal] [IsElementaryAbelian 3 P] {s : ℕ}
    (d : SupportFactors (movedModule ρ P).toRepresentation P s) :
    ∀ g : G, ∀ i, ∃ j, (d.ambient i).conjBy g = d.ambient j := by
  classical
  let W := movedModule ρ P
  let σ := W.toRepresentation
  let := Representation.BinaryGroupAction.action ρ
  let := Representation.BinaryGroupAction.elementary (V := V)
  let := Representation.BinaryGroupAction.faithful ρ hf
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : CommGroup P := IsMulCommutative.instCommGroup
  have hodd : Odd (Nat.card P) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 3 P).exists_card_eq
    exact hn ▸ (by decide : Odd 3).pow
  have hle (i : Fin s) : d.ambient i ≤ P := map_subtype_le _
  have hmove (i : Fin s) :
      (subspaceCommutator σ ⊤ (d.ambient i)).map W.toSubmodule.subtype =
        subspaceCommutator ρ ⊤ (d.ambient i) :=
    movedModule_commutator_map ρ P hodd _ (hle i)
  have hcan (i : Fin s) : d.ambient i ∈ smallSupportFactors G (Multiplicative V) 1 := by
    have hp : P ≤ fittingSubgroup G := le_sSup ⟨inferInstance,inferInstance⟩
    refine ⟨(hle i).trans hp, (card_map_of_injective P.subtype_injective).trans (d.card_factor i),?_⟩
    rw [Representation.BinaryGroupAction.commutator_card]
    congr 1
    have he := (Submodule.equivMapOfInjective W.toSubmodule.subtype
      W.toSubmodule.subtype_injective (subspaceCommutator σ ⊤ (d.ambient i))).finrank_eq
    rw [hmove i] at he
    exact he.symm.trans (d.support_dim i)
  have hall {X : Subgroup G} (hXP : X ≤ P)
      (hX : X ∈ smallSupportFactors G (Multiplicative V) 1) : ∃ i, X = d.ambient i := by
    by_contra hn
    have hne (i : Fin s) : X ≠ d.ambient i := fun he => hn ⟨i,he⟩
    have hfix (i : Fin s) : subspaceCommutator ρ ⊤ (d.ambient i) ≤ fixedSpace ρ X := by
      have hh := smallSupportFactors_cross_fixed (V := Multiplicative V) (Or.inl rfl)
        hX (hcan i) (hne i)
      rw [Representation.BinaryGroupAction.commutator_eq,
        Representation.BinaryGroupAction.fixedPoints_eq] at hh
      exact (Representation.BinaryGroupAction.submoduleEquivSubgroup (V := V)).le_iff_le.mp hh
    have hx1 (x : X) : (x : G) = 1 := by
      apply (moved_faithful ρ hf P hodd).le
      refine ⟨hXP x.property,fun v hv => ?_⟩
      obtain ⟨w,hw⟩ := d.add_bijective.2 (⟨v,hv⟩ : W.toSubmodule)
      have he : ∑ i, ((w i : W.toSubmodule) : V) = v := by
        simpa only [Submodule.coe_sum] using congrArg (fun w : W.toSubmodule => (w : V)) hw
      rw [← he,map_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact hfix i (hmove i ▸ Submodule.mem_map_of_mem (w i).property) x
    have hb : X = ⊥ := le_bot_iff.mp fun x hx => hx1 ⟨x,hx⟩
    have hc := hX.2.1
    rw [hb,card_bot] at hc
    norm_num at hc
  intro g i
  apply hall
  · rintro x ⟨y,hy,rfl⟩
    exact (inferInstance : P.Normal).conj_mem y (hle i hy) g
  · exact smallSupportFactors_conjBy (hcan i) g

/-- The actual old noncyclic actor yields canonical support planes on [V,O₃].
The fixed complement is retained in all minimum-ratio arguments. -/
theorem source_supports
    {H : Type*} [Group H] [Finite H] {K : GroupClass} (hH : IsSQTK K H)
    (f : H →* G) (honto : Function.Surjective f)
    (hf : Function.Injective ρ) {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    (hr : 1 < rank A)
    (hF : generalizedFitting G = fittingSubgroup G) (hcore : pCore 2 G = ⊥) :
    ∃ s : ℕ, (s = 2 ∨ s = 3) ∧
      ∃ d : SupportFactors (movedModule ρ (pCore 3 G)).toRepresentation (pCore 3 G) s,
        (∀ g : G, ∀ i, ∃ j, (d.ambient i).conjBy g = d.ambient j) ∧
        (s = 3 → ∀ i, A ≤ normalizer (d.ambient i : Set G)) := by
  let P := pCore 3 G
  let L := P ⊔ A
  let σ := (movedModule ρ P).toRepresentation
  obtain ⟨s,h⟩ := source_local_input ρ hH f honto hf hA hr hF hcore
  obtain ⟨d,hn⟩ := h.supports _
  change SupportFactors (σ.comp L.subtype) (P.subgroupOf L) s at d
  change s = 3 → ∀ i, A.subgroupOf L ≤ normalizer (d.ambient i : Set L) at hn
  let D := d.ofSubgroup σ (show P ≤ L from le_sup_left)
  let : IsElementaryAbelian 3 (P.subgroupOf L) := h.elementary
  let : IsElementaryAbelian 3 P := IsElementaryAbelian.of_surjective
    (subgroupOfEquivOfLe (show P ≤ L from le_sup_left)).toMonoidHom
    (subgroupOfEquivOfLe (show P ≤ L from le_sup_left)).surjective
  refine ⟨s,h.rank_cases,D,moved_factors_permuted ρ hf P D,?_⟩
  intro hs i
  change A ≤ normalizer ((d.ofSubgroup σ le_sup_left).ambient i : Set G)
  rw [SupportFactors.ofSubgroup_ambient]
  have hh := (map_mono (hn hs i)).trans
    ((d.ambient i).le_normalizer_map L.subtype)
  rw [map_subgroupOf_eq_of_le (show A ≤ L from le_sup_right)] at hh
  exact hh

end CFSG.Quasithin.ChapterD.BeforeMoved

namespace CFSG.Quasithin.ChapterD.BeforeMoved
open Subgroup Representation.BinaryOffender FittingConfigurations Theory.GroupTheory
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)
  {H : Type*} [Group H] [Finite H] {K : GroupClass} (hH : IsSQTK K H)
  (f : H →* G) (honto : Function.Surjective f)
  (hf : Function.Injective ρ) {A : Subgroup G} (hA : A ∈ QhatStar ρ)
  (hr : 1 < rank A)
  (hF : generalizedFitting G = fittingSubgroup G) (hcore : pCore 2 G = ⊥)

include hH f honto hf hA hr hF hcore in
/-- The fourth powers in the old actor's normal closure lie in the actual Fitting subgroup. -/
theorem source_normalClosure_fourth_mem_fitting {n : G}
    (hn : n ∈ normalClosure (A : Set G)) : n ^ 4 ∈ fittingSubgroup G := by
  obtain ⟨s,hs,d,hperm,hthree⟩ := source_supports ρ hH f honto hf hA hr hF hcore
  have hcP := normalClosure_fourth_centralizes _ d hs hperm hthree hn
  let Q := SourceReduction.oddComplement G
  let : Q.Normal := by unfold Q SourceReduction.oddComplement; infer_instance
  have hAQ : A ≤ centralizer (Q : Set G) := le_centralizer_iff.mp
    (SourceReduction.complement_centralizes ρ hf hA hr hcore)
  have hNQ : normalClosure (A : Set G) ≤ centralizer (Q : Set G) :=
    normalClosure_le_normal hAQ
  have hcF : n ^ 4 ∈ centralizer (fittingSubgroup G : Set G) := by
    rw [SourceReduction.fitting_eq_three_sup_complement]
    intro x hx
    obtain ⟨p,hp,q,hq,rfl⟩ := mem_sup_of_normal_left.mp hx
    have hp' := hcP p hp
    have hq' := hNQ ((normalClosure (A : Set G)).pow_mem hn 4) q hq
    rw [mul_assoc,hq',← mul_assoc,hp',mul_assoc]
  have hle : centralizer (fittingSubgroup G : Set G) ≤ fittingSubgroup G := by
    simpa only [hF] using centralizer_generalizedFitting_le G
  exact hle hcF

include hH f honto hf hA hr hF hcore in
/-- Each original noncyclic starred actor generates a normal two-subgroup
in G/F(G), without deleting the original Fitting fixed complement. -/
theorem source_normalClosure_image_two :
    IsPGroup 2 ((normalClosure (A : Set G)).map (QuotientGroup.mk' (fittingSubgroup G))) := by
  intro x
  obtain ⟨n,hn,he⟩ := x.property
  refine ⟨2,Subtype.ext ?_⟩
  change (x : G ⧸ fittingSubgroup G) ^ 4 = 1
  rw [← he,← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr
    (source_normalClosure_fourth_mem_fitting ρ hH f honto hf hA hr hF hcore hn)

include hH f honto hf hA hr hF hcore in
/-- The literal normal-closure image lands in O₂(G/F(G)); this is the
per-actor input for joining the original starred family in 15.1.2. -/
theorem source_normalClosure_le_twoCore_preimage :
    normalClosure (A : Set G) ≤ (pCore 2 (G ⧸ fittingSubgroup G)).comap
      (QuotientGroup.mk' (fittingSubgroup G)) := by
  apply map_le_iff_le_comap.mp
  exact le_sSup ⟨Normal.map inferInstance _ (QuotientGroup.mk'_surjective _),
    source_normalClosure_image_two ρ hH f honto hf hA hr hF hcore⟩

end CFSG.Quasithin.ChapterD.BeforeMoved
