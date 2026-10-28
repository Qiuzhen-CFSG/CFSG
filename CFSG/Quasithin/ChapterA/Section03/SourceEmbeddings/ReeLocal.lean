module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BenderSylowOvergroups
public import Theory.GroupTheory.CComponent.SylowOvergroupUniqueExtensions
public import Theory.GroupTheory.SolvableSylowOvergroups
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Basic
public import Theory.SpecificGroups.ReeF4.LocalPrimeRank
public import Theory.SpecificGroups.ReeF4.CubicRank
public import Theory.SpecificGroups.ReeF4.OddSupplement
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.LocalIdentification
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.PerfectSeeds

/-!
# Local components in the two Ree parabolics

The actual full-Sylow overgroup theorem places a proper local component in
one of the two root parabolics. Perfectness puts it in the local residual;
solvability of proper full-Sylow overgroups in its PSL₂ or Suzuki quotient
then identifies it with that residual. The same quotient calculation proves
uniqueness of C-components in full-Sylow overgroups of the containing carrier.
The ambient C-component condition is inherited from the application, so no
independent simplicity certification is required.

A prime dividing q-1 occurs in either residual quotient and has rank at
least two in the ambient two-coordinate split torus. This includes the
three-free Suzuki residual. The literal Chapter 10 application is in
HalfUniqueness/Components/ReeContaining.
Source: Aschbacher--Smith A.3.12 and 10.2.6, pp.47--48,748--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ReeLocal
open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds
open BenderSuzuki.MatrixGroups

private theorem perfect_le_local {m : ℕ} (s : Side)
    (B : Subgroup (Model m)) [Group.IsPerfect B] (hB : B ≤ parabolic m s) :
    B ≤ localFactor m s := by
  let P := parabolic m s
  let N := (localFactor m s).subgroupOf P
  let H := (borel m).subgroupOf P
  let : Group.IsSolvable (borel m) := OddSupplement.borel_isSolvable m
  let : Group.IsSolvable H := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (borel_le_parabolic m s)).toMonoidHom)
    (subgroupOfEquivOfLe (borel_le_parabolic m s)).injective
  have hsup : N ⊔ H = ⊤ := by
    apply map_injective P.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (localFactor_le_parabolic m s),
      map_subgroupOf_eq_of_le (borel_le_parabolic m s),
      ← parabolic_eq_localFactor_sup_borel, ← MonoidHom.range_eq_map, range_subtype]
  let q := QuotientGroup.mk' N
  have hq : Function.Surjective (q.comp H.subtype) := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, range_subtype]
    have hNq : N.map q = ⊥ := (map_eq_bot_iff N).mpr (by rw [QuotientGroup.ker_mk'])
    have hh := congrArg (map q) hsup
    simpa only [Subgroup.map_sup, hNq, bot_sup_eq,
      map_top_of_surjective q (QuotientGroup.mk'_surjective N)] using hh
  let : Group.IsSolvable (P ⧸ N) := Group.isSolvable_of_surjective hq
  let : Group.IsPerfect (B.subgroupOf P) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hB).symm.toMonoidHom) (subgroupOfEquivOfLe hB).symm.surjective
  have hh := le_of_isPerfect_of_solvable_quotient (B.subgroupOf P) N
  intro x hx
  exact hh (show (⟨x,hB hx⟩ : P) ∈ B.subgroupOf P from hx)


private theorem local_solvable_overgroups {m : ℕ} (hm : 1 ≤ m) (s : Side) :
    SolvableSylowOvergroups (localFactor m s) := by
  apply isSolvable_proper_sylow_overgroup_of_twoCore_quotient
  cases s with
  | linear =>
    exact isSolvable_proper_sylow_overgroup_of_equiv
      ((linearLocalQuotientEquiv m).trans
        (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := CoefficientField m)).symm)
      Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup
  | suzuki =>
    exact isSolvable_proper_sylow_overgroup_of_equiv (suzukiLocalQuotientEquiv m)
      (bender_solvable_proper_sylow_overgroup (.suzuki m hm ⟨MulEquiv.refl _⟩))

private theorem local_top_component {m : ℕ} (hm : 1 ≤ m) (s : Side) :
    (⊤ : Subgroup (localFactor m s)).IsCComponent := by
  let := OuterLocal.localFactor_perfect hm s
  let : IsSimpleGroup (localFactor m s ⧸ pCore 2 (localFactor m s)) := by
    cases s with
    | suzuki =>
      exact (suzukiLocalQuotientEquiv m).isSimpleGroup_congr.mpr
        (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
    | linear =>
      let e := (linearLocalQuotientEquiv m).trans
        (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := CoefficientField m)).symm
      apply e.isSimpleGroup_congr.mpr
      apply Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_simple
      rw [field_card]
      exact lt_of_lt_of_le (by decide : 2 < 2 ^ 3)
        (Nat.pow_le_pow_right (by decide) (by omega))
  let N := pCore 2 (localFactor m s)
  let : Group.IsNilpotent N := pCore_isNilpotent
  let : IsSimpleGroup (⊤ : Subgroup (localFactor m s ⧸ N)) := topEquiv.isSimpleGroup
  let : Group.IsPerfect (⊤ : Subgroup (localFactor m s ⧸ N)) :=
    Group.IsPerfect.ofSurjective (f := (topEquiv (G := localFactor m s ⧸ N)).symm.toMonoidHom)
      (topEquiv (G := localFactor m s ⧸ N)).symm.surjective
  have ht : (⊤ : Subgroup (localFactor m s ⧸ N)).IsCComponent :=
    isCComponent_of_isSimpleGroup_of_isPerfect .top
  obtain ⟨C,hC,he⟩ := ht.exists_map_quotient_eq N
  have hs : C ⊔ N = ⊤ := by
    simpa only [comap_map_eq,QuotientGroup.ker_mk',comap_top] using
      congrArg (Subgroup.comap (QuotientGroup.mk' N)) he
  let := hC.perfect
  have hc : C = ⊤ := (hC.subnormal.eq_solvableResidual_of_sup_eq_top N hs).trans
    Subgroup.solvableResidual_eq_top
  exact hc ▸ hC

/-- Each original local residual has unique C-components in its full-Sylow overgroups. -/
theorem local_sylow_unique {m : ℕ} (hm : 1 ≤ m) (s : Side) :
    SylowOvergroupComponentUnique (localFactor m s) := by
  intro S P hSP B C hB hC
  by_cases he : P = ⊤
  · subst P
    exact ((local_top_component hm s).eq_top_of_isCComponent hB).trans
      ((local_top_component hm s).eq_top_of_isCComponent hC).symm
  · let := local_solvable_overgroups hm s S P hSP he
    exact (hB.not_isSolvable inferInstance).elim

/-- The solvable Borel supplements the local factor inside each literal parabolic. -/
theorem parabolic_sylow_unique {m : ℕ} (hm : 1 ≤ m) (s : Side) :
    SylowOvergroupComponentUnique (parabolic m s) := by
  let : Group.IsSolvable (borel m) := OddSupplement.borel_isSolvable m
  exact SylowOvergroupComponentUnique.of_solvable_supplement
    (localFactor m s) (borel m) (parabolic m s)
    (localFactor_le_parabolic m s) (borel_le_parabolic m s)
    (parabolic_eq_localFactor_sup_borel m s).symm (local_sylow_unique hm s)

/-- Uniqueness uses the inherited top C-component, not a new model-simplicity premise. -/
theorem sylow_unique {m : ℕ} (hm : 1 ≤ m)
    (htop : (⊤ : Subgroup (Model m)).IsCComponent) :
    SylowOvergroupComponentUnique (Model m) := by
  intro S P hSP B C hB hC
  by_cases he : P = ⊤
  · subst P
    exact (htop.eq_top_of_isCComponent hB).trans (htop.eq_top_of_isCComponent hC).symm
  obtain ⟨g,hg⟩ := ThreeSylowContainment.exists_conjugate_eq_unipotent S
  let a := MulAut.conj g
  have hp : P.map a.toMonoidHom ≠ ⊤ := by
    intro ht
    apply he
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [ht,map_top_of_surjective _ a.surjective]
  obtain ⟨s,hs⟩ := OddSupplement.le_parabolic m hm (P.map a.toMonoidHom)
    (hg ▸ map_mono hSP) hp
  rw [MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.parabolic_eq_rootParabolic] at hs
  let e := a.subgroupMap P
  apply map_injective (f := e.toMonoidHom) e.injective
  exact SylowOvergroupComponentUnique.eq_of_le_overgroup (S.mapSurjective a.surjective)
    (map_mono hSP) hs (parabolic_sylow_unique hm s) (hB.map_equiv e) (hC.map_equiv e)

private theorem local_eq_of_le {m : ℕ} (hm : 1 ≤ m) (s : Side)
    (S : Sylow 2 (Model m)) (B : Subgroup (Model m))
    (hB : B ∈ localCComponents S) (hBK : B ≤ localFactor m s)
    (hSK : (S : Subgroup (Model m)) ≤ localFactor m s) : B = localFactor m s := by
  let K := localFactor m s
  let P := B ⊔ (S : Subgroup (Model m))
  have hPK : P ≤ K := sup_le hBK hSK
  have he : P.subgroupOf K = ⊤ := by
    by_contra hn
    let := local_solvable_overgroups hm s (S.subtype hSK) (P.subgroupOf K)
      (fun _ hx => (show (S : Subgroup (Model m)) ≤ P from le_sup_right) hx) hn
    let : Group.IsSolvable P := Group.isSolvable_of_surjective
      (f := (subgroupOfEquivOfLe hPK).toMonoidHom) (subgroupOfEquivOfLe hPK).surjective
    exact hB.not_isSolvable inferInstance
  have heP : P = K := le_antisymm hPK (subgroupOf_eq_top.mp he)
  have hc : (B.subgroupOf K).IsCComponent := by
    change (B.subgroupOf P).IsCComponent at hB
    rwa [heP] at hB
  have hctop : B.subgroupOf K = ⊤ := by
    have hc' : ((B.subgroupOf K).map (topEquiv (G := K)).symm.toMonoidHom).IsCComponent :=
      hc.map_equiv (topEquiv (G := K)).symm
    have hh := (local_top_component hm s).eq_top_of_isCComponent hc'
    apply map_injective (f := (topEquiv (G := K)).symm.toMonoidHom) (topEquiv (G := K)).symm.injective
    simpa only [map_top_of_surjective (topEquiv (G := K)).symm.toMonoidHom (topEquiv (G := K)).symm.surjective] using hh
  exact le_antisymm hBK (subgroupOf_eq_top.mp hctop)

/-- Both residuals, including the three-free Suzuki one, occur with the actual marking. -/
theorem local_placement {m : ℕ} (hm : 1 ≤ m)
    (htop : (⊤ : Subgroup (Model m)).IsCComponent)
    (S : Sylow 2 (Model m)) (B : Subgroup (Model m))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤) :
    ∃ (g : Model m) (s : Side), B.map (MulAut.conj g).toMonoidHom = localFactor m s := by
  have hjoin : B ⊔ (S : Subgroup (Model m)) ≠ ⊤ := by
    intro he
    change (B.subgroupOf (B ⊔ (S : Subgroup (Model m)))).IsCComponent at hB
    rw [he] at hB
    exact hproper (le_antisymm le_top
      (subgroupOf_eq_top.mp (htop.eq_top_of_isCComponent hB)))
  obtain ⟨g,hg⟩ := ThreeSylowContainment.exists_conjugate_eq_unipotent S
  let a := MulAut.conj g
  let R := S.mapSurjective (f := a.toMonoidHom) a.surjective
  let C := B.map a.toMonoidHom
  let : Group.IsSolvable a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]
    infer_instance
  have hC : C ∈ localCComponents R :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hB a.toMonoidHom
  let := hC.perfect
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show C ≤ C ⊔ (R : Subgroup _) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective
  have hp : (B ⊔ (S : Subgroup (Model m))).map a.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hjoin
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [ht,map_top_of_surjective _ a.surjective]
  obtain ⟨s,hs⟩ := OddSupplement.le_parabolic m hm _ (hg ▸ map_mono le_sup_right) hp
  rw [MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.parabolic_eq_rootParabolic] at hs
  refine ⟨g,s,local_eq_of_le hm s R C hC
    (perfect_le_local s C ((map_mono le_sup_left).trans hs)) ?_⟩
  change (S : Subgroup (Model m)).map a.toMonoidHom ≤ _
  rw [hg]
  exact unipotent_le_localFactor m s

/-- Every actual local component shares an odd prime of ambient rank at least two.
The Suzuki parabolic uses a prime of q-1, with no cubic-divisor assumption. -/
theorem shared_prime_rank {m : ℕ} (hm : 1 ≤ m)
    (htop : (⊤ : Subgroup (Model m)).IsCComponent)
    (S : Sylow 2 (Model m)) (B : Subgroup (Model m))
    (hB : B ∈ localCComponents S) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ Nat.card (B ⧸ pCore 2 B) ∧
      2 ≤ primeRank p (Model m) := by
  by_cases ht : B = ⊤
  · subst B
    refine ⟨3,by decide,by decide,?_,CubicRank.model m⟩
    by_contra hn
    have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hn
    rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup,
      primeRank_equiv 3 (topEquiv (G := Model m))] at hz
    have hr := CubicRank.model m
    omega
  obtain ⟨g,s,he⟩ := local_placement hm htop S B hB ht
  let e := ((MulAut.conj g).subgroupMap B).trans (MulEquiv.subgroupCongr he)
  let eq := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  obtain ⟨p,hp,ho,hd,hr⟩ := ReeF4.LocalPrimeRank.local_quotient_shared_prime hm s
  exact ⟨p,hp,ho,(Nat.card_congr eq.toEquiv).symm ▸ hd,hr⟩

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ReeLocal
