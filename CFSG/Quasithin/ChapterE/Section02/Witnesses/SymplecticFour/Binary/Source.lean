module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.Binary.CoreFreePair
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.StrictAction
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalSimpleImage

/-!
# The original binary symplectic witness and strict action bound

For a normal component whose image modulo the full minimal-parabolic core is
Sp₄(2)′, the elementary image either has order two, yielding the original
involution/dihedral witness, or determines the marked four in Aut(A₆).
The latter constructs a literal S₆ = Sp₄(2) conjugate pair. The full-core lift
preserves its quotient map and central Sylow marking, so the established
numeric model theorem applies to every original normalizing overgroup of T.

This discharges the binary branch of GLS, *The Classification of the Finite
Simple Groups*, Vol. II, E.2.7–9 and E.2.15 (printed pp. 219–222, 228), without
assuming a witness, a marked placement, or an automorphism-group model.
-/

public section

namespace CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour.Binary
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
local notation "Sp2" => Theory.SpecificGroups.SymplecticFour.Sp (ZMod 2)
variable {H : Type*} [Group H] [Finite H]

/-- Construct the original dihedral or binary symplectic pair from the actual
normal component and full minimal-parabolic core. -/
theorem source_original (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (eK : K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)) ≃*
      commutator (ClassicalGroup.PSp 2 (ZMod 2)))
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP) :
    Nonempty (BenderPlacement.OriginalWitness T (ChapterB.minimalParabolicMax T hP) V 1) ∨
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
  by_cases hw : Nat.card W = 2
  · obtain ⟨w⟩ := Involution.source_star_order_two T hP V hVT hn hVM hw
    exact Or.inl ⟨BenderPlacement.OriginalWitness.of_dihedral w⟩
  have hWne : W ≠ ⊥ := by
    intro he
    exact hout (by simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff V).mp he)
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
  refine Or.inr ⟨w',e'.trans ξ,S,?_⟩
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

/-- The binary component forces a strict cubic-ratio bound on the same
canonical action of any original normalizing overgroup containing T. -/
theorem source_cubicRatio_lt_two (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (eK : K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)) ≃*
      commutator (ClassicalGroup.PSp 2 (ZMod 2)))
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H)
    (hTI : ∀ g ∈ ChapterB.minimalParabolicMax T hP,
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨ V.map (MulAut.conj g).toMonoidHom = V)
    (U : Subgroup H) (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H)) :
    cubicRatio (DihedralCubic.canonicalAction U V hU) < 2 := by
  rcases source_original T hP hs K hK hgen eK V hVT hn hVM hout with hb | ⟨w,ξ,S,hVS⟩
  · obtain ⟨w⟩ := hb
    exact BenderPlacement.original_witness_cubicRatio_lt_two hP hVT hn hVM hout hfit hTI w hTU hU
  · have hTV := (normal_subgroupOf_iff_le_normalizer hVT).mp hn
    have hNV := minimalParabolic_normalizer_le T hP V
      (IsElementaryAbelian.isPGroup 2 V) hTV hout
    have hh := w.hypotheses hVT hTV hVM hNV
    have hp := w.proper_of_quotient_card_ne_one hNV (by
      rw [Nat.card_congr ξ.toEquiv,Theory.SpecificGroups.SymplecticFour.Binary.card_sp_two]
      decide)
    let := DihedralCubic.centralizer_normal U V hU
    exact (DihedralCubic.ambient_cubic_actor_strict_symplectic_four_of_positive_exponent
      w.le hU hh (w.sylow_eq.le.trans (inf_le_left.trans hTU)) hp (w.fitting hTV hfit)
      1 (by decide) (by simp) ξ S hVS (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)).2.2.2.2.2
end CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour.Binary
