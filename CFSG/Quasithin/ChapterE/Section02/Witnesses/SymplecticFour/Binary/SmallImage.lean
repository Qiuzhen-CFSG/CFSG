module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.Binary.Source
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.SymplecticBinary.SmallAutomizer

/-!
# The original binary symplectic image is cyclic under a small automizer

A noncyclic image in the actual quotient H/J determines the marked elementary
four in Aut(A6). Its literal S6 conjugate pair lifts through the full maximal
core. The small-automizer theorem makes the pair core elementary and forces
cubic ratio at most one. Thus the original nontrivial image has order two.

Source: Aschbacher--Smith E.2.17, printed pp.229--230, using E.2.7--9.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour.Binary
open TwoConjugate
local notation "Sp2" => Theory.SpecificGroups.SymplecticFour.Sp (ZMod 2)
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]

private theorem source_pair_of_noncyclic (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (eK : K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)) ≃*
      commutator (ClassicalGroup.PSp 2 (ZMod 2)))
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hw : Nat.card (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) ≠ 2) :
    ∃ w : QuotientLift.Pair T (ChapterB.minimalParabolicMax T hP) V,
    ∃ ξ : (w.subgroup ⧸ ((ChapterB.minimalParabolicMax T hP).subgroupOf w.subgroup).normalCore) ≃* Sp2,
    ∃ S : Sylow 2 Sp2,
      (V.subgroupOf w.subgroup).map (ξ.toMonoidHom.comp (QuotientGroup.mk' _)) ≤
        (center S).map (S : Subgroup Sp2).subtype := by
  let M := ChapterB.minimalParabolicMax T hP
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let T' := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let D := K.map q
  let W := V.map q
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  have hWne : W ≠ ⊥ := by
    intro he
    exact hout (by simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff V).mp he)
  change Nat.card W ≠ 2 at hw
  have hW : 2 < Nat.card W := by
    have hh := (one_lt_card_iff_ne_bot W).mpr hWne
    omega
  have hi := Structure.source_normal_simple_image T hP hs K hK hgen
  let : IsSimpleGroup D := hi.1
  let : D.Normal := hi.2.2.1
  let hp' := ChapterB.minimalParabolic_surjective_core T hP q
    (QuotientGroup.mk'_surjective J) (by rw [QuotientGroup.ker_mk'])
  have hj' : ChapterB.minimalParabolicCore T' hp' = ⊥ :=
    (Structure.source_star_minimal_core_free T hP).2
  have hm' : ChapterB.minimalParabolicMax T' hp' = M.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q
      (QuotientGroup.mk'_surjective J) (by rw [QuotientGroup.ker_mk'])).symm
  have hWT : W ≤ (T' : Subgroup (H ⧸ J)) := map_mono hVT
  have hTW : (T' : Subgroup (H ⧸ J)) ≤ normalizer (W : Set (H ⧸ J)) :=
    (map_mono ((normal_subgroupOf_iff_le_normalizer hVT).mp hn)).trans (le_normalizer_map q)
  let eD := eK.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix
  obtain ⟨e,P,hT,hV,_⟩ := coreFree_full_action T' hp' hj' D hi.2.1 hi.2.2.2 eD W hWT hTW hW
  have hp := pair_of_marked_aut T' hp' W hWT e P hT hV
  rw [hm'] at hp
  obtain ⟨w,ξ,S,hVS⟩ := hp
  obtain ⟨w',r,_,hr,e',he'⟩ := QuotientLift.lift_pair T hP V hVT hn hVM w
  refine ⟨w',e'.trans ξ,S,?_⟩
  have hrV : (V.subgroupOf w'.subgroup).map r = W.subgroupOf w.subgroup := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      change (r x : H ⧸ J) ∈ W
      rw [hr]
      exact mem_map_of_mem q hx
    · intro hy
      obtain ⟨x,hx,hxy⟩ := hy
      let z : w'.subgroup := ⟨x,w'.le hx⟩
      refine ⟨z,hx,Subtype.ext ?_⟩
      rw [hr]
      exact hxy
  have hemap : (e'.trans ξ).toMonoidHom.comp (QuotientGroup.mk' _) =
      (ξ.toMonoidHom.comp (QuotientGroup.mk' _)).comp r := by
    apply MonoidHom.ext
    intro x
    change ξ (e' (QuotientGroup.mk' _ x)) = ξ (QuotientGroup.mk' _ (r x))
    rw [he']
  rw [hemap,←map_map,hrV]
  exact hVS

theorem source_image_card_two
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (eK : K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)) ≃*
      commutator (ClassicalGroup.PSp 2 (ZMod 2)))
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H)
    (U : Subgroup H) (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (f : U →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (V : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U V hU f hf hk)) :
    Nat.card (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) = 2 := by
  by_contra hw
  obtain ⟨w,ξ,S,hVS⟩ := source_pair_of_noncyclic T hP hs K hK hgen eK V hVT hvn hcore hout hw
  have hTV := (normal_subgroupOf_iff_le_normalizer hVT).mp hvn
  have hNV := minimalParabolic_normalizer_le T hP V
    (IsElementaryAbelian.isPGroup 2 V) hTV hout
  let h := w.hypotheses hVT hTV hcore hNV
  let hSU := w.sylow_eq.le.trans (inf_le_left.trans hTU)
  let e := subgroupOfEquivOfLe w.le
  let ρ := DihedralCubic.representation U V hU f hf hk
  let fA := DihedralCubic.actorMap h hSU f
  have hp := w.proper_of_quotient_card_ne_one hNV (by
    rw [Nat.card_congr ξ.toEquiv,Theory.SpecificGroups.SymplecticFour.Binary.card_sp_two]
    decide)
  apply h.binary_symplectic_small_automizer_false hp (w.fitting hTV hfit)
    ξ S hVS e ρ (DihedralCubic.representation_injective U V hU f hf hk) fA ?_ hD hratio
  intro a v
  apply Subtype.ext
  change ((ρ (f (DihedralCubic.actorIn h hSU a)) (Additive.ofMul (e v))).toMul : H) =
    ((a : w.subgroup) : H) * ((v : w.subgroup) : H) * ((a : w.subgroup) : H)⁻¹
  rw [DihedralCubic.representation_apply]
  rfl
end CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour.Binary
