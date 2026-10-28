module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.PairedHall
public import Theory.SpecificGroups.SL2.FullPairTorus

/-!
# Full torus coordinates on the original Hall subgroup

The original orbit quotient sends the prescribed Sylow normalizer into
an SL₂ pair Borel. Its two-core misses the odd Hall. Since that Hall has
order `(q - 1)^2`, simultaneous diagonalization identifies it with the
full pair of multiplicative groups. Its two literal projection kernels
are cyclic of order `q - 1`, disjoint, and generate the original Hall.
The final theorem constructs the quotient marking on L and its prescribed
Sylow conjugate; it introduces no separately selected Hall subgroup.

Natural marking and Borel placement remain the earlier obligations of the
moving-Hall assembly. Matching the comparison component's Hall intersection
to one of these axes and constructing the terminal geometry remain there.
Source: Aschbacher–Smith 10.2.3(4), printed pp.746–747.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false
include D in
private theorem orbit_sylow_intersection :
    ∃ S : Sylow 2 (localOrbit T L),
      (S : Subgroup (localOrbit T L)) = (T : Subgroup G).subgroupOf (localOrbit T L) := by
  let R := localOrbit T L
  let M := D.maximalLocal
  let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  obtain ⟨P,hP⟩ := (T.subtype (le_normalizer_componentOrbit L T)).exists_subgroupOf_eq_of_normal
    (R.subgroupOf M)
  let a := subgroupOfEquivOfLe R.le_normalizer
  refine ⟨P.mapSurjective (f := a.toMonoidHom) a.surjective,?_⟩
  change (P : Subgroup (R.subgroupOf M)).map a.toMonoidHom = _
  rw [hP]
  ext r
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact hx
  · intro hr
    exact ⟨⟨⟨r,R.le_normalizer r.property⟩,r.property⟩,hr,rfl⟩


/-- The original Hall is the full split torus, with its literal quotient axes. -/
theorem Context.hall_torus_of_quotient
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L)
    (a : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* (SL(2,F) × SL(2,F))) :
    let C := B.map H.subtype
    let hCR : C ≤ localOrbit T L := hBB.trans ((map_subtype_le _).trans inf_le_left)
    let f := (a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localOrbit T L)))).comp (inclusion hCR)
    let f₁ := (MonoidHom.fst SL(2,F) SL(2,F)).comp f
    let f₂ := (MonoidHom.snd SL(2,F) SL(2,F)).comp f
    (∃ (u v : SL(2,F)) (d : C ≃* Fˣ × Fˣ),
      ∀ x : C, ((MulAut.conj u).prodCongr (MulAut.conj v)) (f x) =
        (SpecialLinearGroup.diag2 ((d x).1 : F) (Units.ne_zero _),
          SpecialLinearGroup.diag2 ((d x).2 : F) (Units.ne_zero _))) ∧
      Nat.card (f₁.ker.map C.subtype) = Nat.card F - 1 ∧
      Nat.card (f₂.ker.map C.subtype) = Nat.card F - 1 ∧
      Disjoint (f₁.ker.map C.subtype) (f₂.ker.map C.subtype) ∧
      f₁.ker.map C.subtype ⊔ f₂.ker.map C.subtype = C ∧
      IsCyclic (f₁.ker.map C.subtype) ∧ IsCyclic (f₂.ker.map C.subtype) := by
  let R := localOrbit T L
  let C := B.map H.subtype
  have hCN : C ≤ sourceOrbitSylowNormalizer T L := hBB.trans (map_subtype_le _)
  have hCR : C ≤ R := hCN.trans inf_le_left
  have hodd : Odd (Nat.card C) := ctx.odd_card_of_le_hall_image C le_rfl
  let q : R →* (SL(2,F) × SL(2,F)) := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
  have hq : Function.Surjective q := a.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 R := by
    ext x
    change a (QuotientGroup.mk' _ x) = 1 ↔ _
    rw [a.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let f : C →* (SL(2,F) × SL(2,F)) := q.comp (inclusion hCR)
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_of_card_eq
    have hp : IsPGroup 2 f.ker := by
      change IsPGroup 2 (q.ker.comap (inclusion hCR))
      rw [hk]
      exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hCR)
    exact hp.card_eq_or_dvd.resolve_right
      (hodd.of_dvd_nat (card_subgroup_dvd_card f.ker)).not_two_dvd_nat
  obtain ⟨S,hS⟩ := orbit_sylow_intersection D
  have hN : (sourceOrbitSylowNormalizer T L).subgroupOf R =
      normalizer ((S : Subgroup R) : Set R) := by
    have he : (sourceOrbitSylowNormalizer T L).subgroupOf R =
        (normalizer (((T : Subgroup G) ⊓ R : Subgroup G) : Set G)).subgroupOf R := by
      ext x
      exact and_iff_right x.property
    rw [he,subgroupOf_normalizer_eq (show (T : Subgroup G) ⊓ R ≤ R from inf_le_right)]
    congr 2
    rw [hS]
    ext x
    exact and_iff_left x.property
  let P := S.mapSurjective hq
  have hBN : f.range ≤ normalizer ((P : Subgroup (SL(2,F) × SL(2,F))) : Set _) := by
    rintro _ ⟨b,rfl⟩
    apply (S : Subgroup R).le_normalizer_map q
    apply mem_map.mpr
    refine ⟨inclusion hCR b,?_,rfl⟩
    rw [←hN]
    exact hCN b.property
  have hcard : Nat.card C = (Nat.card F - 1)^2 := by
    rw [show C = B.map H.subtype from rfl,card_map_of_injective H.subtype_injective]
    exact ctx.hall_card_eq_torus_square D n hn hF e mark hBB
  have htorus := SpecialLinearGroup.full_pair_borel_torus_coordinates P f hi hBN hodd hcard
  obtain ⟨h₁,h₂,hd,hs,hcy₁,hcy₂⟩ :=
    SpecialLinearGroup.full_pair_borel_coordinate_kernels P f hi hBN hodd hcard
  let f₁ := (MonoidHom.fst SL(2,F) SL(2,F)).comp f
  let f₂ := (MonoidHom.snd SL(2,F) SL(2,F)).comp f
  dsimp only
  refine ⟨htorus,?_,?_,Subgroup.disjoint_map C.subtype_injective hd,?_,?_,?_⟩
  · rw [card_map_of_injective C.subtype_injective]
    exact h₁
  · rw [card_map_of_injective C.subtype_injective]
    exact h₂
  · rw [←Subgroup.map_sup,hs,←MonoidHom.range_eq_map,range_subtype]
  · let := hcy₁
    exact isCyclic_of_surjective (f₁.ker.equivMapOfInjective C.subtype C.subtype_injective).toMonoidHom
      (f₁.ker.equivMapOfInjective C.subtype C.subtype_injective).surjective
  · let := hcy₂
    exact isCyclic_of_surjective (f₂.ker.equivMapOfInjective C.subtype C.subtype_injective).toMonoidHom
      (f₂.ker.equivMapOfInjective C.subtype C.subtype_injective).surjective

/-- Construct the quotient and both full axes on the two original components. -/
theorem Context.original_hall_torus
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L) :
    ∃ (t : G) (ht : t ∈ (T : Subgroup G)), t ∉ normalizer (L : Set G) ∧
      ∃ a : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* (SL(2,F) × SL(2,F)),
        (∀ l : L, a (QuotientGroup.mk' _ ⟨l,le_componentOrbit L T l.property⟩) =
          (e (QuotientGroup.mk' _ l),1)) ∧
        (∀ l : L, a (QuotientGroup.mk' _ (originalConjugateOrbitInclusion ht l)) =
          (1,e (QuotientGroup.mk' _ l))) ∧
    let C := B.map H.subtype
    let hCR : C ≤ localOrbit T L := hBB.trans ((map_subtype_le _).trans inf_le_left)
    let f := (a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localOrbit T L)))).comp (inclusion hCR)
    let f₁ := (MonoidHom.fst SL(2,F) SL(2,F)).comp f
    let f₂ := (MonoidHom.snd SL(2,F) SL(2,F)).comp f
    (∃ (u v : SL(2,F)) (d : C ≃* Fˣ × Fˣ),
      ∀ x : C, ((MulAut.conj u).prodCongr (MulAut.conj v)) (f x) =
        (SpecialLinearGroup.diag2 ((d x).1 : F) (Units.ne_zero _),
          SpecialLinearGroup.diag2 ((d x).2 : F) (Units.ne_zero _))) ∧
      Nat.card (f₁.ker.map C.subtype) = Nat.card F - 1 ∧
      Nat.card (f₂.ker.map C.subtype) = Nat.card F - 1 ∧
      Disjoint (f₁.ker.map C.subtype) (f₂.ker.map C.subtype) ∧
      f₁.ker.map C.subtype ⊔ f₂.ker.map C.subtype = C ∧
      IsCyclic (f₁.ker.map C.subtype) ∧ IsCyclic (f₂.ker.map C.subtype) := by
  obtain ⟨t,ht,htn,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 ctx.nonnormal
  obtain ⟨a,hfirst,hsecond⟩ := source_original_natural_pair_quotient D n hn hF e ctx.nonnormal ht htn
  exact ⟨t,ht,htn,a,hfirst,hsecond,ctx.hall_torus_of_quotient D n hn hF e mark hBB a⟩

end CFSG.Quasithin.Chapter10.MovingHall
