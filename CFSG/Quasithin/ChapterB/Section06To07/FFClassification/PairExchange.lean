module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorPermutation
public import CFSG.Quasithin.ChapterB.Section06To07.OffenderGeneration
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd
/-!
# The original Sylow exchanges the two B.5.6 factors

In a minimal parabolic with trivial two-core, its maximal-overgroup core is
nilpotent. A nontrivial centerless normal subgroup cannot lie in this core;
it therefore supplements the Sylow. Any disjoint centerless factor then
embeds in a two-group quotient, an impossibility. Apply this to the original
B.5.6 product: intrinsic factor permutation together with absence of exchange
would make its first factor normal. Hence the prescribed Sylow exchanges the
two literal factors. The final theorem discharges original offender generation.

Source: Aschbacher–Smith B.6.8(2),(4), B.6.9 and E.2.3, pp.114–116 and 216–217.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
open SourceInduction
variable {G : Type*} [Group G] [Finite G]
/-- The original maximal-overgroup core is nilpotent when the two-core is trivial. -/
theorem minimalParabolic_core_nilpotent_of_twoCore_eq_bot
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤) (hcore : pCore 2 G = ⊥) :
    Group.IsNilpotent (minimalParabolicCore T hP) := by
  let J := minimalParabolicCore T hP
  let q := QuotientGroup.mk' (pCore 2 G)
  have hq : Function.Injective q := (q.ker_eq_bot_iff).mp ((QuotientGroup.ker_mk' _).trans hcore)
  let e := J.equivMapOfInjective q hq
  let : Group.IsNilpotent (J.map q) := minimalParabolic_coreImage_nilpotent T hP
  exact Group.nilpotent_of_mulEquiv e.symm

/-- A centerless normal factor cannot have a disjoint nontrivial centerless companion. -/
theorem minimalParabolic_not_normal_centerless_disjoint
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤) (hcore : pCore 2 G = ⊥)
    (A B : Subgroup G) [Nontrivial A] [Nontrivial B]
    (hA : center A = ⊥) (hB : center B = ⊥) (hd : Disjoint A B) [A.Normal] : False := by
  have hnot : ¬ A ≤ minimalParabolicCore T hP := by
    intro ha
    let : Group.IsNilpotent (minimalParabolicCore T hP) :=
      minimalParabolic_core_nilpotent_of_twoCore_eq_bot T hP hcore
    let : Group.IsNilpotent A := Group.nilpotent_of_mulEquiv (subgroupOfEquivOfLe ha)
    exact Group.IsNilpotent.center_ne_bot A hA
  obtain ha | ht := minimalParabolic_normal_subgroup_dichotomy T hP A
  · exact hnot ha
  let q := QuotientGroup.mk' A
  have hm := congrArg (map q) ht
  have hmap : (T : Subgroup G).map q = ⊤ := by
    have hk : A.map q = ⊥ := by simpa only [q,QuotientGroup.ker_mk'] using (map_ker_self q)
    simpa only [Subgroup.map_sup,hk,sup_bot_eq,
      map_top_of_surjective q (QuotientGroup.mk'_surjective A)] using hm
  have hp : IsPGroup 2 (G ⧸ A) :=
    (show IsPGroup 2 (⊤ : Subgroup (G ⧸ A)) from hmap ▸ T.isPGroup'.map q).of_equiv topEquiv
  have hb : Function.Injective (q.comp B.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    change x = 1
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hd
      ((QuotientGroup.eq_one_iff _).mp hx) x.property
  let : Group.IsNilpotent B := (hp.of_injective (q.comp B.subtype) hb).isNilpotent
  exact Group.IsNilpotent.center_ne_bot B hB
private theorem centerless_of_equiv {H E : Type*} [Group H] [Group E]
    (e : H ≃* E) (hz : center E = ⊥) : center H = ⊥ := by
  apply (eq_bot_iff_forall _).mpr
  intro x hx
  have he : e x = 1 := hz.le (by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z,rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hx z))
  exact e.injective (he.trans e.map_one.symm)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
/-- The prescribed Sylow exchanges the same two factors in the source product. -/
theorem source_two_factor_exists_sylow_exchange
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤) (hcore : pCore 2 G = ⊥)
    (Y : Subgroup G) [Y.Normal] (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (ρ : Representation (ZMod 2) Y V) (d : SourceTwoFactorCase ρ) :
    ∃ t : T, d.first.map (MulAut.conjNormal (t : G)).toMonoidHom = d.second ∧
      d.second.map (MulAut.conjNormal (t : G)).toMonoidHom = d.first := by
  classical
  have hcY : pCore 2 Y = ⊥ := by
    have hle : (pCore 2 Y).map Y.subtype ≤ pCore 2 G :=
      le_sSup ⟨inferInstance,pCore_isPGroup.map Y.subtype⟩
    rw [hcore] at hle
    apply bot_unique
    intro x hx
    exact Subtype.ext (hle (mem_map_of_mem Y.subtype hx))
  by_contra hn
  have hfix (t : T) : d.first.map (MulAut.conjNormal (t : G)).toMonoidHom = d.first := by
    rcases d.automorphism_permutation hcY (MulAut.conjNormal (t : G)) with hh | hh
    · exact hh.1
    · exact (hn ⟨t,hh⟩).elim
  let A := d.first.map Y.subtype
  let B := d.second.map Y.subtype
  let eA := d.first.equivMapOfInjective Y.subtype Y.subtype_injective
  let eB := d.second.equivMapOfInjective Y.subtype Y.subtype_injective
  let : Nontrivial d.first := d.firstCase.nontrivial
  let : Nontrivial d.second := d.secondCase.nontrivial
  let : Nontrivial A := eA.injective.nontrivial
  let : Nontrivial B := eB.injective.nontrivial
  let : d.first.Normal := d.product.swap.second_normal
  have hYA : Y ≤ normalizer (A : Set G) := by
    intro y hy
    apply d.first.le_normalizer_map Y.subtype
    exact ⟨⟨y,hy⟩,by rw [d.first.normalizer_eq_top]; trivial,rfl⟩
  have hTA : (T : Subgroup G) ≤ normalizer (A : Set G) := by
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hh := congrArg (map Y.subtype) (hfix ⟨t,ht⟩)
    rw [map_map] at hh
    have he : Y.subtype.comp (MulAut.conjNormal t).toMonoidHom =
        (MulAut.conj t).toMonoidHom.comp Y.subtype := by ext; rfl
    rw [he,← map_map] at hh
    exact hh
  let : A.Normal := normalizer_eq_top_iff.mp
    (top_unique (hgen ▸ sup_le hYA hTA))
  have hd : Disjoint A B := by
    apply disjoint_iff.mpr
    rw [show A = d.first.map Y.subtype from rfl,show B = d.second.map Y.subtype from rfl,
      ← map_inf _ _ _ Y.subtype_injective,d.product.disjoint.eq_bot,Subgroup.map_bot]
  exact minimalParabolic_not_normal_centerless_disjoint T hP hcore A B
    (centerless_of_equiv eA.symm d.firstCase.center_eq_bot)
    (centerless_of_equiv eB.symm d.secondCase.center_eq_bot) hd
/-- The exchange witness belongs to the prescribed Sylow of the actual original offender action. -/
theorem source_offender_two_factor_exists_sylow_exchange [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hff : IsFFModule ρ) (hcore : pCore 2 G = ⊥)
    (d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype)) :
    letI := offenderSubgroup_normal ρ
    ∃ t : T, d.first.map (MulAut.conjNormal (t : G)).toMonoidHom = d.second ∧
      d.second.map (MulAut.conjNormal (t : G)).toMonoidHom = d.first := by
  let := offenderSubgroup_normal ρ
  exact source_two_factor_exists_sylow_exchange T hP hcore _
    (offender_generation T hP ρ hff hcore).2 _ d
end CFSG.Quasithin.ChapterB
