module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.SylowUniqueContaining
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ReeLocal

/-!
# Excluding the Ree containing-component pair

Full-Sylow component uniqueness proves that the two containing components
are distinct. The literal image of either original factor is a local
component in the Ree quotient. Its intrinsic quotient retains an odd split
torus prime of rank at least two in Ree, contradicting the rank-one bound
contributed by the other factor. This covers both the linear and Suzuki
parabolics and does not impose a cubic divisor on Suzuki.

The original exchanger, half-join and relative normal containing components
are unchanged. All local recognition and distinctness premises in this row
are discharged. Remaining containing rows, Suzuki enlargement in other
models, the zero-kernel binary-three normalizer and final assembly stay with
qt-d-10-nona5-half-sylow-unique. The final source boundary permits only
ModuleChoiceAt from qt-d-10-nona5-point-selection, with its final discharge
retained by qt-d-10-nona5-point-control.
Source: Aschbacher--Smith A.3.12 and 10.2.6, pp.47--48,748--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}

private theorem top_component_quotient_model {A X : Type*} [Group A] [Finite A] [Group X]
    (ht : (⊤ : Subgroup A).IsCComponent) (d : (A ⧸ pCore 2 A) ≃* X) :
    (⊤ : Subgroup X).IsCComponent := by
  let : Group.IsNilpotent (pCore 2 A) := pCore_isNilpotent
  have h := (ht.map_quotient (pCore 2 A)).map_equiv d
  simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
    map_top_of_surjective d.toMonoidHom d.surjective] using h

/-- The actual original factor retains a prime of rank at least two in its Ree overcomponent. -/
theorem ContainingPair.shared_prime_of_ree_quotient
    (C : ContainingPair D H t K₁ K₂)
    {s : G} (hs : s ∈ (T : Subgroup G)) {K : Subgroup G}
    (hK : K ∈ cComponentsIn H)
    (hBK : L.map (MulAut.conj s).toMonoidHom ≤ K)
    {m : ℕ} (hm : 1 ≤ m) (d : (K ⧸ pCore 2 K) ≃* ReeF4.Model m) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ Nat.card (L ⧸ pCore 2 L) ∧
      2 ≤ primeRank p K := by
  obtain ⟨S,_,hl⟩ := C.local_sylow_in_containing hs hK hBK
  let B := (L.map (MulAut.conj s).toMonoidHom).subgroupOf K
  let b : L ≃* B := ((MulAut.conj s).subgroupMap L).trans (subgroupOfEquivOfLe hBK).symm
  let q := d.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := d.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ d.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent q.ker := hk.symm ▸ pCore_isNilpotent
  have hA : B.map q ∈ localCComponents (S.mapSurjective hq) :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hl q
  have ht : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.2.subgroupOf_of_le le_rfl hK.1
  obtain ⟨p,hp,ho,hd,hr⟩ := SourceEmbeddings.ReeLocal.shared_prime_rank hm
    (top_component_quotient_model ht d) (S.mapSurjective hq) (B.map q) hA
  let : Fact p.Prime := ⟨hp⟩
  have hkb : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap,hk]
    exact pCore_isPGroup.comap_of_injective B.subtype B.subtype_injective
  let eb := (q.subgroupMap B).quotientPCoreEquivOfSurjective (q.subgroupMap_surjective B) hkb
  let e := (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans eb
  refine ⟨p,hp,ho,(Nat.card_congr e.toEquiv).symm ▸ hd,?_⟩
  rw [←primeRank_equiv p d] at hr
  exact hr.trans (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup)

/-- Exclude the first actual Ree quotient, proving distinctness internally. -/
theorem ContainingPair.impossible_of_first_ree_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {m : ℕ} (hm : 1 ≤ m) (d : (K₁ ⧸ pCore 2 K₁) ≃* ReeF4.Model m) : False := by
  have ht : (⊤ : Subgroup K₁).IsCComponent := by
    simpa only [subgroupOf_self] using C.first_component.subgroupOf le_rfl
  have hne := C.distinct_of_first_sylow_unique_quotient d
    (SourceEmbeddings.ReeLocal.sylow_unique hm (top_component_quotient_model ht d))
  have hmap : (K₁.map H.subtype).subgroupOf H = K₁ :=
    comap_map_eq_self_of_injective H.subtype_injective K₁
  have hK : K₁.map H.subtype ∈ cComponentsIn H :=
    ⟨map_subtype_le _,hmap.symm ▸ C.first_component⟩
  have hLK : L.map (MulAut.conj (1 : G)).toMonoidHom ≤ K₁.map H.subtype := by
    have hh := map_mono (f := H.subtype) C.first_le
    have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x; simp
    simpa only [hid,Subgroup.map_id,map_subgroupOf_eq_of_le C.left_le] using hh
  let a := (K₁.equivMapOfInjective H.subtype H.subtype_injective).symm
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans d
  obtain ⟨p,hp,ho,hd,hr⟩ := C.shared_prime_of_ree_quotient (one_mem _) hK hLK hm b
  let : Fact p.Prime := ⟨hp⟩
  rw [primeRank_equiv p a] at hr
  have hl := (C.odd_ranks hn hne ho hd).1
  omega

/-- Exclude the second actual Ree quotient with the original source exchanger. -/
theorem ContainingPair.impossible_of_second_ree_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {m : ℕ} (hm : 1 ≤ m) (d : (K₂ ⧸ pCore 2 K₂) ≃* ReeF4.Model m) : False := by
  have ht : (⊤ : Subgroup K₂).IsCComponent := by
    simpa only [subgroupOf_self] using C.second_component.subgroupOf le_rfl
  have hne := C.distinct_of_second_sylow_unique_quotient d
    (SourceEmbeddings.ReeLocal.sylow_unique hm (top_component_quotient_model ht d))
  have hmap : (K₂.map H.subtype).subgroupOf H = K₂ :=
    comap_map_eq_self_of_injective H.subtype_injective K₂
  have hK : K₂.map H.subtype ∈ cComponentsIn H :=
    ⟨map_subtype_le _,hmap.symm ▸ C.second_component⟩
  have hLK : L.map (MulAut.conj t).toMonoidHom ≤ K₂.map H.subtype := by
    simpa only [map_subgroupOf_eq_of_le C.right_le] using map_mono (f := H.subtype) C.second_le
  let a := (K₂.equivMapOfInjective H.subtype H.subtype_injective).symm
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans d
  obtain ⟨p,hp,ho,hd,hr⟩ := C.shared_prime_of_ree_quotient C.t_mem hK hLK hm b
  let : Fact p.Prime := ⟨hp⟩
  rw [primeRank_equiv p a] at hr
  have hl := (C.odd_ranks hn hne ho hd).2
  omega

/-- Either actual Ree containing quotient contradicts the source containing pair. -/
theorem ContainingPair.impossible_of_ree_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {m : ℕ} (hm : 1 ≤ m)
    (he : Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* ReeF4.Model m) ∨
      Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* ReeF4.Model m)) : False := by
  rcases he with he | he
  all_goals obtain ⟨e⟩ := he
  · exact C.impossible_of_first_ree_quotient hn hm e
  · exact C.impossible_of_second_ree_quotient hn hm e

/-- The exact Theorem C model predicate supplies either literal Ree quotient. -/
theorem ContainingPair.impossible_of_ree_model
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {m : ℕ} (hm : 1 ≤ m)
    (he : Chapter1.Section02.LocalModels.IsReeF4At (K₁ ⧸ pCore 2 K₁) m ∨
      Chapter1.Section02.LocalModels.IsReeF4At (K₂ ⧸ pCore 2 K₂) m) : False := by
  apply C.impossible_of_ree_quotient hn hm
  rcases he with ⟨d,⟨e⟩⟩ | ⟨d,⟨e⟩⟩
  · exact .inl ⟨e.trans d.modelEquiv⟩
  · exact .inr ⟨e.trans d.modelEquiv⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
