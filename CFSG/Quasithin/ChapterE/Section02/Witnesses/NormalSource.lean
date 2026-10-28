module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.FullCenterSource
public import Theory.SpecificGroups.SymplecticFour.BorelActionGeometry.TorusInvariant
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.StrictSourceNonbinary

/-!
# Cubic bounds for a module normalized by the marked maximal subgroup

Normality supplies the full Borel torus on the original nonbinary symplectic
image. Its two independent root weights split every invariant subgroup into
root axes, and the moving Sylow actor excludes each single axis. The image
is therefore the full central plane. Its established opposite pair lifts
through the original maximal core and supplies a strict cubic actor in any
normalizing overgroup of the original Sylow subgroup.

The final theorem combines this argument with the other original E.2 model
rows. Its additional normalization premise holds for V(M) in 15.1.1, so no
recognition of smaller arbitrary symplectic subgroups is needed by that
consumer. Source: Aschbacher--Smith E.2.7--9 and E.2.13--15, printed
pp.219--228; 3.1.6, printed pp.573--574.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
open Theory.SpecificGroups.SymplecticFour DiagramAutomorphisms EvenBorelTorus TwoConjugate
open ChapterB Representation.OneCohomology.SymplecticFour CentralRootGeometry
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The marked normal source subgroup is the full central root plane. -/
theorem source_normal_full_card {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hJ : minimalParabolicCore T hP = ⊥)
    (L : Subgroup G) [L.Normal] [IsSimpleGroup L] (e : L ≃* Sp F)
    (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hVM : V ≤ (minimalParabolicMax T hP).pCoreIn 2)
    (hVN : minimalParabolicMax T hP ≤ normalizer (V : Set G))
    (hne : V ≠ ⊥) : Nat.card V = (Nat.card F)^2 := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2 = 2^1) ▸ Nat.pow_lt_pow_right (by decide) hn
  obtain ⟨g,hmark,_,hB⟩ := Structure.SymplecticFour.source_diagram_and_borel hF hn T hP L e hgen
  let e' := (e.trans (MulAut.conj g)).symm
  let f := L.subtype.comp e'.toMonoidHom
  let W := V.comap f
  have hf : Function.Injective f := L.subtype_injective.comp e'.injective
  have hVL := Structure.SymplecticFour.source_inner_placement hF hn T hP hJ L e' hmark hgen V hVT hVM
  have hfr : f.range = L := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e'.surjective,
      ← MonoidHom.range_eq_map,range_subtype]
  have hmap : W.map f = V := by rw [map_comap_eq,hfr,inf_eq_right.mpr hVL]
  have hWne : W ≠ ⊥ := by
    intro he
    apply hne
    rw [← hmap,he,Subgroup.map_bot]
  let j : W →* V := (f.comp W.subtype).codRestrict V (fun x => x.property)
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (hf (congrArg (fun z : V => (z : G)) he))
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective j hj
  have hWU : W ≤ unipotent := by
    rw [← hmark]
    exact comap_mono hVT
  obtain ⟨t,ht⟩ := Structure.SymplecticFour.exists_moving_sylow_actor hF hn T hP L e' hmark hgen
  let a : ActorReduction.stabilizer (F := F) :=
    ⟨extensionAction L e' t, Structure.SymplecticFour.sylow_actor T L e' hmark t⟩
  have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) :=
    (minimalParabolicMax_spec T hP).2.trans hVN
  have hWa : W.map a.val.toMonoidHom = W := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      change f (a.val x) ∈ V
      rw [show f (a.val x) = t.val * f x * t.val⁻¹ from extensionAction_apply L e' t x]
      exact (mem_normalizer_iff.mp (hTV t.property) (f x)).mp hx
    · rw [card_map_of_injective a.val.injective]
  have hcenter := elementary_le_center_of_moving_actor hF hn a.val a.property ht W hWU hWa
  have htorus : (diagonalTorusHom (F := F)).range ≤ normalizer (W : Set (Sp F)) := by
    apply le_normalizer_iff.mpr
    rintro x ⟨u,rfl⟩ w hw
    change f (diagonalTorusHom u * w * (diagonalTorusHom u)⁻¹) ∈ V
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hVN (hB.ge (diagonalTorus_mem_borel u.1 u.2))) (f w)).mp hw
  obtain ⟨hl,hs⟩ := not_root_axes_of_moving_actor hq a ht W hWa hWne
  have hfull : W = CentralRootGeometry.parameter.range := by
    rcases BorelActionGeometry.invariant_subgroup_cases hq W
      (hcenter.trans_eq CentralRootGeometry.parameter_range.symm) htorus with h|h|h|h
    · exact (hWne h).elim
    · exact (hl h.le).elim
    · exact (hs h.le).elim
    · exact h
  rw [← hmap,card_map_of_injective hf,hfull,BorelActionGeometry.card_centralPlane]


variable {H : Type*} [Group H] [Finite H]

/-- The same full-center pair on the literal quotient by the maximal core. -/
theorem source_normal_full_quotient
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) ≃*
      ClassicalGroup.PSp 2 F)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hVN : ChapterB.minimalParabolicMax T hP ≤ normalizer (V : Set H)) :
    Nonempty (NativeWitness
      (T.mapSurjective (QuotientGroup.mk'_surjective (ChapterB.minimalParabolicCore T hP)))
      ((ChapterB.minimalParabolicMax T hP).map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)))
      (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) F) := by
  let J := ChapterB.minimalParabolicCore T hP
  let M := ChapterB.minimalParabolicMax T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let W := V.map q
  let L := K.map q
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  obtain ⟨hLs,hLa,hLn,hLT⟩ := Structure.source_normal_simple_image T hP hs K hK hgen
  let : IsSimpleGroup L := hLs
  let : L.Normal := hLn
  have hmin : ChapterB.IsMinimalParabolicOver S ⊤ := (Structure.source_star_minimal_core_free T hP).1
  have hcore : ChapterB.minimalParabolicCore S hmin = ⊥ := (Structure.source_star_minimal_core_free T hP).2
  have hmax : ChapterB.minimalParabolicMax S hmin = M.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'])).symm
  have hWcore : W ≤ (ChapterB.minimalParabolicMax S hmin).pCoreIn 2 := by
    rw [hmax]
    exact (map_mono hVM).trans (Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.core_image_le q M)
  have hWN : ChapterB.minimalParabolicMax S hmin ≤ normalizer (W : Set (H ⧸ J)) := by
    rw [hmax]
    exact (map_mono hVN).trans (le_normalizer_map q)
  have hWne : W ≠ ⊥ := by
    intro he
    exact hout (by simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff V).mp he)
  have hcard : Nat.card W = (Nat.card F)^2 :=
    source_normal_full_card hF hn S hmin hcore L (e.trans EvenProjective.equiv.symm)
      hLT W (map_mono hVT) hWcore hWN hWne
  apply source_full_center_quotient T hP hs K hK hgen hn hF e V hVT
    ((normal_subgroupOf_iff_le_normalizer hVT).mpr ((minimalParabolicMax_spec T hP).2.trans hVN)) hVM
  exact (by simpa only [hF] using hcard.ge)


open Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative

theorem source_normal_cubicRatio_lt_two
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSp
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 (2^n))
    (V U : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hVN : ChapterB.minimalParabolicMax T hP ≤ normalizer (V : Set H))
    (hfit : generalizedFitting H = pCore 2 H)
    (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H)) :
    cubicRatio (DihedralCubic.canonicalAction U V hU) < 2 := by
  obtain ⟨F,hF,hfin,hFcard,⟨e⟩⟩ := hm
  let : CharP F 2 := EvenProjective.charTwo_of_card hFcard
  obtain ⟨w⟩ := source_normal_full_quotient T hP hs K hK hgen hn hFcard e V hVT hVM hout hVN
  let M := ChapterB.minimalParabolicMax T hP
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  have hTV : (T : Subgroup H) ≤ normalizer (V : Set H) := (minimalParabolicMax_spec T hP).2.trans hVN
  have hvn := (normal_subgroupOf_iff_le_normalizer hVT).mpr hTV
  have hNV := minimalParabolic_normalizer_le T hP V (IsElementaryAbelian.isPGroup 2 V) hTV hout
  obtain ⟨w',r,_,hr,ξ,hξ⟩ := QuotientLift.lift_pair T hP V hVT hvn hVM w.pair
  have hrV : (V.subgroupOf w'.subgroup).map r = (V.map q).subgroupOf w.pair.subgroup := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      change (r x : H ⧸ J) ∈ V.map q
      rw [hr]
      exact mem_map_of_mem q hx
    · intro hy
      obtain ⟨x,hx,hxy⟩ := hy
      let z : w'.subgroup := ⟨x,w'.le hx⟩
      refine ⟨z,hx,Subtype.ext ?_⟩
      rw [hr]
      exact hxy
  have hξmap : (ξ.trans w.quotientModel).toMonoidHom.comp (QuotientGroup.mk' _) =
      (w.quotientModel.toMonoidHom.comp (QuotientGroup.mk' _)).comp r := by
    apply MonoidHom.ext
    intro x
    change w.quotientModel (ξ (QuotientGroup.mk' _ x)) = w.quotientModel (QuotientGroup.mk' _ (r x))
    rw [hξ]
  have hVS : (V.subgroupOf w'.subgroup).map ((ξ.trans w.quotientModel).toMonoidHom.comp
      (QuotientGroup.mk' _)) ≤
      (center (unipotentSylow hFcard (by omega : 1 ≤ n))).map
        (unipotentSylow hFcard (by omega : 1 ≤ n) : Subgroup (Sp F)).subtype := by
    rw [hξmap,←map_map,hrV]
    exact w.quotient_center hFcard (by omega)
  have hproper := w'.proper_of_quotient_card_ne_one hNV (by
    rw [Nat.card_congr (ξ.trans w.quotientModel).toEquiv]
    have hd : 2 ∣ Nat.card (Sp F) := by
      rw [card_sp,hFcard]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
        ((dvd_pow_self 2 (by omega : n ≠ 0)).trans (dvd_pow_self _ (by decide : 4 ≠ 0))) _) _
    intro he
    rw [he] at hd
    norm_num at hd)
  let := DihedralCubic.centralizer_normal U V hU
  exact (DihedralCubic.ambient_cubic_actor_strict_symplectic_four_of_positive_exponent
    w'.le hU (w'.hypotheses hVT hTV hVM hNV)
    (w'.sylow_eq.le.trans (inf_le_left.trans hTU)) hproper (w'.fitting hTV hfit)
    n (by omega) hFcard (ξ.trans w.quotientModel) (unipotentSylow hFcard (by omega)) hVS
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)).2.2.2.2.2

end CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour

namespace CFSG.Quasithin.ChapterE.Witnesses
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation.BinaryOffender
universe u
variable {H : Type u} [Group H] [Finite H]

theorem source_normal_cubicRatio_lt_two
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (V U : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hVN : ChapterB.minimalParabolicMax T hP ≤ normalizer (V : Set H))
    (hfit : generalizedFitting H = pCore 2 H)
    (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H)) :
    cubicRatio (DihedralCubic.canonicalAction U V hU) < 2 := by
  have hvn := (normal_subgroupOf_iff_le_normalizer hVT).mpr
    ((ChapterB.minimalParabolicMax_spec T hP).2.trans hVN)
  have hTI : ∀ g ∈ ChapterB.minimalParabolicMax T hP,
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨ V.map (MulAut.conj g).toMonoidHom = V := by
    intro g hg
    exact Or.inr ((mem_normalizer_iff_map_conj_eq).mp (hVN hg))
  rcases source_cubicRatio_lt_two_or_nonbinary_symplectic hH T hP V U hVT hvn hVM hout hfit hTI hTU hU
    with hb | ⟨K,hK,hN,hgen,n,hn,hm⟩
  · exact hb
  let := hN
  have hs : ¬ Group.IsSolvable H := by
    intro h
    let := h
    exact hK.not_isSolvable
      (Group.isSolvable_of_isSolvable_injective (f := K.subtype) K.subtype_injective)
  exact SymplecticFour.source_normal_cubicRatio_lt_two T hP hs K hK hgen (by omega) hm
    V U hVT hVM hout hVN hfit hTU hU

end CFSG.Quasithin.ChapterE.Witnesses

