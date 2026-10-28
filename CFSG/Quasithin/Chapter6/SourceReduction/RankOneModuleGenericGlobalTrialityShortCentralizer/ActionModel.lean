module
public import Theory.SpecificGroups.Triality.ShortRootCentralizer.Action
public import Theory.GroupTheory.EmbeddedCenterMap
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.UniqueFixedCosetQuotient
public import CFSG.Quasithin.ChapterI.Section06To08.UniqueFixedSource

/-!
# The triality long-root plane and its ambient automizer

An injective image of the central parabolic carries its characteristic
long-root plane into the centralizer of the marked short root. The central
Levi is perfect and acts nontrivially when q > 2, so this action has
nonsolvable image. Native transitivity reduces I.8.5 to the unique fixed
coset condition for the pinned highest long root. The cosets are those of
the actual short-root centralizer, with relative normality proved there.

This is the action part of Aschbacher–Smith F.4.42, printed p.295
(`refs/quasithin.pdf`). The unique fixed coset remains an explicit premise;
this module does not assert full ambient short-root containment.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.RadicalCoordinates Triality.Standard.RadicalCoordinates.LeviCommutators
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityShortAction
namespace Native
abbrev plane := _root_.Triality.Standard.ShortRootCentralizer.plane
end Native
open _root_.Triality.Standard.ShortRootCentralizer
variable {G : Type*} [Group G] [Finite G]

@[expose] def plane {P : Parameters} (f : parabolic P .central →* G) : Subgroup G :=
  ((Native.plane P).subgroupOf (parabolic P .central)).map f

@[expose] def short (P : Parameters) (hp : P.prime = 2) : parabolic P .central :=
  ⟨LeviCommutators.short P hp 2 1,radical_le_parabolic P .central
    (descendedRootSubgroup_le_radical P hp .central (short_mem P hp .central 2 trivial 1))⟩

@[expose] def long (P : Parameters) (hp : P.prime = 2) : parabolic P .central :=
  ⟨LeviCommutators.long P hp 2 1,radical_le_parabolic P .central
    (plane_le_radical P (long_two_mem_plane P hp 1))⟩

omit [Finite G] in
theorem plane_center {P : Parameters} (f : parabolic P .central →* G)
    (hf : Function.Injective f) :
    plane f = (center (((radical P .central).subgroupOf (parabolic P .central)).map f)).map
      (((radical P .central).subgroupOf (parabolic P .central)).map f).subtype := by
  let Q := (radical P .central).subgroupOf (parabolic P .central)
  have he : (Native.plane P).subgroupOf (parabolic P .central) = (center Q).map Q.subtype := by
    apply map_injective (parabolic P .central).subtype_injective
    rw [map_subgroupOf_eq_of_le ((plane_le_radical P).trans (radical_le_parabolic P .central)),
      map_embeddedCenter Q _ (parabolic P .central).subtype_injective,
      map_subgroupOf_eq_of_le (radical_le_parabolic P .central)]
    rfl
  rw [plane,he,map_embeddedCenter Q f hf]

omit [Finite G] in
theorem plane_normalized {P : Parameters} (f : parabolic P .central →* G)
    (hf : Function.Injective f) (N : Subgroup G)
    (hn : N ≤ normalizer (((radical P .central).subgroupOf (parabolic P .central)).map f : Set G)) :
    N ≤ normalizer (plane f : Set G) := by
  rw [plane_center f hf]
  exact hn.trans (normalizer_le_normalizer_characteristic_image _ (center _))

omit [Finite G] in
theorem plane_centralizes {P : Parameters} (hp : P.prime = 2)
    (f : parabolic P .central →* G) : plane f ≤ centralizer ({f (short P hp)} : Set G) := by
  rintro _ ⟨a,ha,rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  rw [←map_mul,←map_mul]
  exact congrArg f (Subtype.ext (mem_centralizer_singleton_iff.mp
    (plane_le_centralizer P hp 1 ha)))

omit [Finite G] in
theorem plane_elementary {P : Parameters} (hp : P.prime = 2)
    (f : parabolic P .central →* G) : IsElementaryAbelian 2 (plane f) := by
  let : IsElementaryAbelian 2 (Native.plane P) :=
    _root_.Triality.Standard.ShortRootCentralizer.plane_elementary P hp
  let : IsElementaryAbelian 2 ((Native.plane P).subgroupOf (parabolic P .central)) :=
    IsElementaryAbelian.subgroupOf ((plane_le_radical P).trans (radical_le_parabolic P .central))
  exact IsElementaryAbelian.map f

omit [Finite G] in
theorem plane_ne_bot {P : Parameters} (hp : P.prime = 2)
    (f : parabolic P .central →* G) (hf : Function.Injective f) : plane f ≠ ⊥ := by
  intro he
  have hh : (Native.plane P).subgroupOf (parabolic P .central) = ⊥ :=
    (map_injective hf) (he.trans (Subgroup.map_bot _).symm)
  have hm := congrArg (fun R : Subgroup (parabolic P .central) => R.map (parabolic P .central).subtype) hh
  rw [map_subgroupOf_eq_of_le ((plane_le_radical P).trans (radical_le_parabolic P .central)),Subgroup.map_bot] at hm
  exact _root_.Triality.Standard.ShortRootCentralizer.plane_ne_bot P hp hm

omit [Finite G] in
theorem action_not_solvable {P : Parameters} (hp : P.prime = 2) (hq : 2 < P.q)
    (f : parabolic P .central →* G) (hf : Function.Injective f)
    (N : Subgroup G) (hN : f.range ≤ N)
    (hn : N ≤ normalizer (((radical P .central).subgroupOf (parabolic P .central)).map f : Set G)) :
    let C := centralizer ({f (short P hp)} : Set G)
    let X := N.subgroupOf C
    let V := (plane f).subgroupOf C
    letI : (V.subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer (by
      intro x hx
      apply mem_normalizer_iff.mpr
      intro a
      exact mem_normalizer_iff.mp (plane_normalized f hf N hn hx) a.val)
    ¬ Group.IsSolvable (X ⧸ centralizer (V.subgroupOf X : Set X)) := by
  dsimp only
  let C := centralizer ({f (short P hp)} : Set G)
  let X := N.subgroupOf C
  let V := (plane f).subgroupOf C
  let : (V.subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer (by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (plane_normalized f hf N hn hx) a.val)
  let k : levi P .central →* X := {
    toFun a := ⟨⟨f ⟨a,levi_le_parabolic P .central a.property⟩,
      mem_centralizer_singleton_iff.mpr (by
        rw [←map_mul,←map_mul]
        exact congrArg f (Subtype.ext (mem_centralizer_singleton_iff.mp
          (levi_central_le_centralizer P hp 1 a.property))))⟩,hN ⟨_,rfl⟩⟩
    map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one f
    map_mul' a b := by
      apply Subtype.ext
      apply Subtype.ext
      exact map_mul f ⟨a.val,levi_le_parabolic P .central a.property⟩
        ⟨b.val,levi_le_parabolic P .central b.property⟩ }
  intro hs
  let : Group.IsSolvable (X ⧸ centralizer (V.subgroupOf X : Set X)) := hs
  let : Group.IsPerfect (levi P .central) := levi_central_isPerfect P hp hq
  let : Group.IsPerfect k.range := Group.IsPerfect.range k
  have hk := le_of_isPerfect_of_solvable_quotient k.range (centralizer (V.subgroupOf X : Set X))
  apply levi_moves_plane P hp hq
  intro a ha b hb
  let bP : parabolic P .central := ⟨b,(radical_le_parabolic P .central) (plane_le_radical P hb)⟩
  have hbV : f bP ∈ plane f := mem_map_of_mem f hb
  let bX : X := ⟨⟨f bP,plane_centralizes hp f hbV⟩,hN ⟨_,rfl⟩⟩
  have hh := hk (show k ⟨a,ha⟩ ∈ k.range from ⟨_,rfl⟩) bX hbV
  have he := congrArg (fun x : X => x.val.val) hh
  change f _ * f _ = f _ * f _ at he
  rw [←map_mul,←map_mul] at he
  exact (congrArg Subtype.val (hf he)).symm

/-- I.8.5 gives containment once the actual plane fixes unique cosets. -/
theorem centralizer_le_of_unique_fixed {P : Parameters} (hp : P.prime = 2) (hq : 2 < P.q)
    (f : parabolic P .central →* G) (hf : Function.Injective f)
    (N : Subgroup G) (hN : f.range ≤ N)
    (hn : N ≤ normalizer (((radical P .central).subgroupOf (parabolic P .central)).map f : Set G))
    (hfix : ∀ v : centralizer ({f (short P hp)} : Set G), v.val ∈ plane f → v ≠ 1 →
      ∃! q : centralizer ({f (short P hp)} : Set G) ⧸ N.subgroupOf
        (centralizer ({f (short P hp)} : Set G)), v • q = q) :
    centralizer ({f (short P hp)} : Set G) ≤ N := by
  let C := centralizer ({f (short P hp)} : Set G)
  let X := N.subgroupOf C
  let V := (plane f).subgroupOf C
  have hVC : plane f ≤ C := plane_centralizes hp f
  let : IsElementaryAbelian 2 (plane f) := plane_elementary hp f
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf hVC
  have hVX : V ≤ X := fun v hv => hN ((map_le_range f _) hv)
  let : (V.subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer (by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (plane_normalized f hf N hn hx) a.val)
  have hVne : V ≠ ⊥ := by
    intro he
    have hh := congrArg (fun R : Subgroup C => R.map C.subtype) he
    rw [map_subgroupOf_eq_of_le hVC,Subgroup.map_bot] at hh
    exact plane_ne_bot hp f hf hh
  by_contra hle
  have hproper : X ≠ ⊤ := by
    intro he
    exact hle (fun x hx => show (⟨x,hx⟩ : C) ∈ X from he ▸ mem_top _)
  exact action_not_solvable hp hq f hf N hN hn
    (ChapterI.Section06To08.lemma_I_8_5_automizer V X hVX hVne hproper hfix)

@[expose] def longMark {P : Parameters} (hp : P.prime = 2)
    (f : parabolic P .central →* G) : centralizer ({f (short P hp)} : Set G) :=
  ⟨f (long P hp),plane_centralizes hp f (mem_map_of_mem f (long_two_mem_plane P hp 1))⟩

/-- Native transitivity transfers the fixed-coset condition from the pinned
long root to the whole plane. -/
theorem centralizer_le_of_long_unique_fixed (m : ℕ) (hm : 0 < m) (hm2 : 1 < m)
    (f : parabolic (binaryParameters m hm) .central →* G) (hf : Function.Injective f)
    (N : Subgroup G) (hN : f.range ≤ N)
    (hn : N ≤ normalizer (((radical (binaryParameters m hm) .central).subgroupOf
      (parabolic (binaryParameters m hm) .central)).map f : Set G))
    (hfix : ∃! q : centralizer ({f (short (binaryParameters m hm) rfl)} : Set G) ⧸ N.subgroupOf
        (centralizer ({f (short (binaryParameters m hm) rfl)} : Set G)),
      longMark rfl f • q=q) :
    centralizer ({f (short (binaryParameters m hm) rfl)} : Set G) ≤ N := by
  let P := binaryParameters m hm
  have hq : 2 < P.q := Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) hm2
  apply centralizer_le_of_unique_fixed rfl hq f hf N hN hn
  intro x hx hx1
  obtain ⟨a,ha,he⟩ := hx
  have ha1 : a.val ≠ 1 := by
    intro hh
    apply hx1
    apply Subtype.ext
    rw [←he,show a=1 from Subtype.ext hh,map_one]
    rfl
  obtain ⟨g,hg,hga⟩ := plane_orbit P rfl 1 a.val ha ha1
  let gP : parabolic P .central := ⟨g,centralizer_le_central m hm hm2 1 one_ne_zero hg⟩
  have hfg : f gP ∈ centralizer ({f (short P rfl)} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    rw [←map_mul,←map_mul]
    exact congrArg f (Subtype.ext (mem_centralizer_singleton_iff.mp hg))
  apply UniqueFixedCoset.unique_of_isConj hfix
  apply isConj_iff.mpr
  refine ⟨⟨f gP,hfg⟩,?_⟩
  apply Subtype.ext
  change f gP*f (long P rfl)*(f gP)⁻¹=x.val
  rw [←map_inv,←map_mul,←map_mul,←he]
  exact congrArg f (Subtype.ext hga)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityShortAction
