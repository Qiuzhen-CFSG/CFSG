module
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.LinearThreeFamily
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.LinearThreeC3Local
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Parabolics.Quotient

/-!
# The middle residue of the original binary-three C₃ family

The literal middle vertex is J=K₀L₂T. Its supplied S₃×S₃ core quotient
makes the Sylow index nine. The source identifies its two edges with
L₂T and K₀T. The cubic quotient of L₂ and Sylow supplementation give
index three in the first edge; the actual S₃ quotient gives index three
in the second. Hence both edges are maximal in J.

The supplied chamber equality identifies their intersection with T.
The two-maximal-overgroup theorem for S₃×S₃, lifted through O₂(J),
then proves the full rank-two subgroup lattice. Finally the canonical
inclusion equivalence transports it to the actual middle vertex of the
source-generated family. The product isomorphism needs no factor markings.

Source: Aschbacher--Smith, 13.7.6(1), printed p.940, using the actual
13.5.4 plane actor and the binary-three point-parabolic calculation.
The product quotient and chamber equality are supplied separately by
LinearThreeC3Product and the endpoint-residue assembly.
-/

public section
open Subgroup Representation Module
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource.LinearThreeMiddleResidue
open Section08.SourceCompletion
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionRecognition.Component.RecognitionStep
open Section08.TransvectionParabolic.Marking
open Section05.PlaneGeometry.TwoBlocks
open LinearThreeC3Local
open CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Parabolics
open Quasithin.I5
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

private theorem sylow_index_core_card (S : Sylow 2 G) :
    S.index * 2 ^ (Nat.card (G ⧸ pCore 2 G)).factorization 2 =
      Nat.card (G ⧸ pCore 2 G) := by
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G))
  have hi : P.index = S.index := (S : Subgroup G).index_map_eq
    (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal S)
  have hc := (P : Subgroup (G ⧸ pCore 2 G)).index_mul_card
  rw [P.card_eq_multiplicity,hi] at hc
  exact hc

private theorem normalized_sylow_intersection (X : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G)) :
    ∃ S : Sylow 2 X, (S : Subgroup X) = (T : Subgroup G).subgroupOf X := by
  let P := X ⊔ (T : Subgroup G)
  have hXP : X ≤ P := le_sup_left
  let : (X.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le X.le_normalizer hn)
  obtain ⟨S,hS⟩ := (T.subtype (show (T : Subgroup G) ≤ P from le_sup_right)).exists_subgroupOf_eq_of_normal
    (X.subgroupOf P)
  let e := subgroupOfEquivOfLe hXP
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change (S : Subgroup (X.subgroupOf P)).map e.toMonoidHom = _
  rw [hS]
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩; exact ha
  · intro hx; exact ⟨⟨⟨x,hXP x.prop⟩,x.prop⟩,hx,rfl⟩

private theorem normalized_cubic_sylow_index (X : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hc : Nat.card (X ⧸ pCore 2 X) = 3) :
    (T : Subgroup G).relIndex (X ⊔ (T : Subgroup G)) = 3 := by
  obtain ⟨S,hS⟩ := normalized_sylow_intersection X hn
  have hi := sylow_index_core_card S
  rw [hc] at hi
  norm_num [show (Nat.factorization 3) 2 = 0 from by decide +kernel] at hi
  let P := X ⊔ (T : Subgroup G)
  let I := X ⊓ (T : Subgroup G)
  have hT := ((T : Subgroup G).subgroupOf P).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show (T : Subgroup G) ≤ P from le_sup_right)).toEquiv] at hT
  have hX := (S : Subgroup X).card_mul_index
  rw [hi,hS] at hX
  have hcI : Nat.card ((T : Subgroup G).subgroupOf X) = Nat.card I :=
    Nat.card_congr {
      toFun := fun x => ⟨x.val.val,⟨x.val.prop,x.prop⟩⟩
      invFun := fun x => ⟨⟨x.val,x.prop.1⟩,x.prop.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [hcI] at hX
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes X (T : Subgroup G) hn
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := (T : Subgroup G)))
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := I))
  calc
    Nat.card I * (Nat.card (T : Subgroup G) * (T : Subgroup G).relIndex P) =
        Nat.card I * Nat.card P := congrArg (Nat.card I * ·) hT
    _ = Nat.card X * Nat.card (T : Subgroup G) := hp.symm
    _ = (Nat.card I * 3) * Nat.card (T : Subgroup G) := by rw [hX]
    _ = Nat.card I * (Nat.card (T : Subgroup G) * 3) := by ac_rfl

/-- The actual L₂T edge has Sylow index three. -/
theorem plane_edge_sylow_index
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥) :
    (T : Subgroup G).relIndex
      (planeActor (L := L) (V₂ := V₂) ⊔ (T : Subgroup G)) = 3 :=
  normalized_cubic_sylow_index _
    (d.plane_stable.trans (Ordinary.source_planeActor_normalized d eL hm))
    (Ordinary.planeActor_core_source d eL).2

/-- The middle product quotient gives Sylow index nine, independently of factor markings. -/
theorem middle_sylow_index
    (eJ : (middle T L K V₂ ⧸ pCore 2 (middle T L K V₂)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    (T : Subgroup G).relIndex (middle T L K V₂) = 9 := by
  have hi := sylow_index_core_card (T.subtype (sylow_le_middle (L := L) (K := K) (V₂ := V₂)))
  have hc : Nat.card (middle T L K V₂ ⧸ pCore 2 (middle T L K V₂)) = 36 := by
    rw [Nat.card_congr eJ.toEquiv,Nat.card_prod,Nat.card_perm,Nat.card_fin]
    decide +kernel
  rw [hc] at hi
  norm_num [show (Nat.factorization 36) 2 = 2 from by decide +kernel] at hi
  change (T : Subgroup G).relIndex (middle T L K V₂) * 4 = 36 at hi
  omega

/-- The two literal source edges are precisely the middle rank-two parabolics. -/
theorem source_middle_rankTwo
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinear.GL (Fin 3 → ZMod 2))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (linearRepresentation 3) eK)
    (eJ : (middle T L K V₂ ⧸ pCore 2 (middle T L K V₂)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (hc : chamberSubgroup (LinearThreeFamily.family (L ⊔ (T : Subgroup G))
        (middle T L K V₂) H) =
      (T : Subgroup G).subgroupOf ((L ⊔ (T : Subgroup G)) ⊔ H)) :
    let F := LinearThreeFamily.family (L ⊔ (T : Subgroup G)) (middle T L K V₂) H
    RankTwoParabolics (F 1) ((chamberSubgroup F).subgroupOf (F 1))
      (localParabolic F 1 0) (localParabolic F 1 2) := by
  let J := middle T L K V₂
  let A := L ⊔ (T : Subgroup G)
  let P := planeActor (L := L) (V₂ := V₂) ⊔ (T : Subgroup G)
  let R := pointResidual K V₂ ⊔ (T : Subgroup G)
  let Ω := A ⊔ H
  have hTJ : (T : Subgroup G).relIndex J = 9 := middle_sylow_index eJ
  obtain ⟨_,⟨eL⟩,_⟩ := ModelExclusions.linear_three_source_setup_of_one_le
    d hH hF9 hKH hK hL₁K ρ hρ eK hs
  have hTP : (T : Subgroup G).relIndex P = 3 := plane_edge_sylow_index d eL hm
  obtain ⟨_,⟨eR⟩⟩ := point_parabolic d hH hF9 hKH hK hL₁K ρ hρ eK hs
  have hTR : (T : Subgroup G).relIndex R = 3 := by
    have hi := sylow_index_core_card (T.subtype (show (T : Subgroup G) ≤ R from le_sup_right))
    have hcard : Nat.card (R ⧸ pCore 2 R) = 6 := by
      rw [Nat.card_congr eR.toEquiv,Nat.card_perm,Nat.card_fin]
      decide +kernel
    rw [hcard] at hi
    norm_num [show (Nat.factorization 6) 2 = 1 from by decide +kernel] at hi
    change (T : Subgroup G).relIndex R * 2 = 6 at hi
    omega
  have hPJ : P ≤ J := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hRJ : R ≤ J := sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hP : (A.subgroupOf J).index = 3 := by
    have hi := relIndex_mul_relIndex (T : Subgroup G) P J le_sup_right hPJ
    rw [hTP,hTJ] at hi
    change A.relIndex J = 3
    rw [←inf_relIndex_right,inf_comm A J,middle_inf_local d]
    change P.relIndex J = 3
    omega
  have hR : (H.subgroupOf J).index = 3 := by
    have hi := relIndex_mul_relIndex (T : Subgroup G) R J le_sup_right hRJ
    rw [hTR,hTJ] at hi
    change H.relIndex J = 3
    rw [←inf_relIndex_right,inf_comm H J,middle_inf_H d hH hF9 hKH hK hL₁K ρ hρ eK hs]
    change R.relIndex J = 3
    omega
  have hJΩ : J ≤ Ω := middle_le_generated hKH
  have hinter : A.subgroupOf J ⊓ H.subgroupOf J = (T : Subgroup G).subgroupOf J := by
    ext x
    have hx := congrArg (fun U : Subgroup Ω => (⟨x,hJΩ x.prop⟩ : Ω) ∈ U) hc
    simpa [chamberSubgroup,LinearThreeFamily.family,Fin.forall_fin_succ,mem_subgroupOf,A,show x.val ∈ middle T L K V₂ from x.prop] using Iff.of_eq hx
  have hres : RankTwoParabolics J ((T : Subgroup G).subgroupOf J)
      (A.subgroupOf J) (H.subgroupOf J) := by
    apply rankTwo_of_prime_indices _ _ _
      (hasTwoMaximalOvergroups_quotient (pCore 2 J) pCore_isPGroup eJ
        hasTwoMaximalOvergroups_product (T.subtype sylow_le_middle))
    · rw [hP]; exact Nat.prime_three
    · rw [hR]; exact Nat.prime_three
    · exact hinter
    · change Nat.card ((T : Subgroup G).subgroupOf J) < Nat.card (A.subgroupOf J)
      have hb := ((T : Subgroup G).subgroupOf J).card_mul_index
      have hp := (A.subgroupOf J).card_mul_index
      change Nat.card ((T : Subgroup G).subgroupOf J) * (T : Subgroup G).relIndex J = Nat.card J at hb
      rw [hTJ] at hb
      rw [hP] at hp
      have hpos := Nat.card_pos (α := (T : Subgroup G).subgroupOf J)
      omega
  dsimp only
  rw [hc]
  exact rankTwo_subgroupOf J A H (T : Subgroup G) Ω hJΩ hres

end CFSG.Quasithin.Chapter13.Section07.OrdinarySource.LinearThreeMiddleResidue
