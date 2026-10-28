module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PointQuotient
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.ActionKernel
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.FourBlockResidual
public import Theory.Quasithin.CoprimeRank

/-!
# The original singular point stabilizer and its three-rank

Map the original Sylow intersection in L through the action-kernel quotient.
The full coordinates identify its fixed point with a four-plus-four partition.
This constructs a surjection from the literal C_L(z) to the even four-block
stabilizer, with the actual conjugation formula and kernel C_L(z) ∩ O₂(L).
The two-group kernel preserves three-rank, giving rank two in C_L(z).
No model label or independent action marking is assumed.

Source: Aschbacher--Smith, the point-centralizer setup preceding 12.6.24
and the Sylow-three subgroup in 12.6.26, printed pp.830--832. The earlier
C_V(L)=1 and T-invariance of the point remain explicit.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
open BinaryPermutation BinaryPermutation.TerminalOrthogonal
variable {G : Type*} [Group G] [Finite G]
  {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis K T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The actual singular point stabilizer map, including its permutation
formula and exact two-core intersection kernel. -/
theorem SourceHypothesis.original_point_stabilizer_map
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G)) :
    ∃ (r : alternatingGroup (Fin 8))
      (f : (L ⊓ (D.fullSetup hZ T z).Gz : Subgroup G) →* FourBlockResidual.P),
      Function.Surjective f ∧
      (∀ c, (f c).val = r.val *
        (D.groupEquiv (QuotientGroup.mk' (conjugation L V S.chosen.normalizes).ker
          ⟨c.val,c.property.1⟩)).val * r.val⁻¹) ∧
      f.ker = (L.pCoreIn 2).subgroupOf (L ⊓ (D.fullSetup hZ T z).Gz) := by
  let E := D.fullSetup hZ T z
  let J := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf J
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer S.chosen.sylow_normalizes_component)
  obtain ⟨P,hP⟩ := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).exists_subgroupOf_eq_of_normal A
  let e : A ≃* L := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  let q : L →* alternatingGroup (Fin 8) := D.groupEquiv.toMonoidHom.comp
    (QuotientGroup.mk' (conjugation L V S.chosen.normalizes).ker)
  have hq : Function.Surjective q := D.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  let fA := q.comp e.toMonoidHom
  let Q := P.mapSurjective (f := fA) (hq.comp e.surjective)
  have hTC : (T : Subgroup G) ≤ E.Gz := hTz.trans
    (normalizer_le_centralizer_of_card_two E.V₁ (E.point_card hz))
  have hfix : ∀ g ∈ (Q : Subgroup (alternatingGroup (Fin 8))),
      naturalRepresentation (Fin 8) g.val (D.fullCoordinates hZ z).toAdd =
        (D.fullCoordinates hZ z).toAdd := by
    rintro g ⟨a,ha,rfl⟩
    have hat : (e a : G) ∈ (T : Subgroup G) := by rw [hP] at ha; exact ha
    have he : conjugation L V S.chosen.normalizes (e a) z = z := by
      apply Subtype.ext
      have hh := hTC hat z.val (mem_zpowers _)
      change (e a : G)*z.val*(e a : G)⁻¹=z.val
      rw [←hh,mul_inv_cancel_right]
    exact (D.fullCoordinates_equivariant hZ (e a) z).symm.trans
      (congrArg (fun v : V => (D.fullCoordinates hZ v).toAdd) he)
  have hn : (D.fullCoordinates hZ z).toAdd ≠ 0 := by
    intro he
    exact hz ((D.fullCoordinates hZ).injective (he.trans (D.fullCoordinates hZ).map_one.symm))
  obtain ⟨r,hr⟩ := Eight.alternating_exists_conjugate_stabilizer Q
    (D.fullCoordinates hZ z).toAdd hn hfix
  have hcentral (l : L) : l.val ∈ E.Gz ↔
      naturalRepresentation (Fin 8) (q l).val (D.fullCoordinates hZ z).toAdd =
        (D.fullCoordinates hZ z).toAdd := by
    rw [E.Gz_eq,mem_centralizer_singleton_iff]
    have he := D.fullCoordinates_equivariant hZ l z
    constructor
    · intro hc
      change l.val*z.val=z.val*l.val at hc
      have hl : conjugation L V S.chosen.normalizes l z = z := by
        apply Subtype.ext
        change l.val*z.val*l.val⁻¹=z.val
        rw [hc,mul_inv_cancel_right]
      exact he.symm.trans (congrArg (fun v : V => (D.fullCoordinates hZ v).toAdd) hl)
    · intro hc
      have hl := (D.fullCoordinates hZ).injective (he.trans hc)
      exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hl)
  let C := L ⊓ E.Gz
  let j : C →* L := inclusion inf_le_left
  let f₀ : C →* Equiv.Perm (Fin 8) :=
    (MulAut.conj r.val).toMonoidHom.comp ((alternatingGroup (Fin 8)).subtype.comp (q.comp j))
  have hf₀ (c : C) : f₀ c ∈ FourBlockResidual.P := by
    refine ⟨?_,(hr _).mp ((hcentral (j c)).mp c.property.2)⟩
    exact (alternatingGroup (Fin 8)).mul_mem
      ((alternatingGroup (Fin 8)).mul_mem r.property (q (j c)).property)
      ((alternatingGroup (Fin 8)).inv_mem r.property)
  let f := f₀.codRestrict FourBlockResidual.P hf₀
  have hf : Function.Surjective f := by
    intro b
    let a : alternatingGroup (Fin 8) := ⟨r.val⁻¹*b.val*r.val,by
      exact (alternatingGroup (Fin 8)).mul_mem
        ((alternatingGroup (Fin 8)).mul_mem
          ((alternatingGroup (Fin 8)).inv_mem r.property) b.property.1) r.property⟩
    obtain ⟨l,hl⟩ := hq a
    have hlC : l.val ∈ E.Gz := by
      apply (hcentral l).mpr
      apply (hr _).mpr
      rw [hl]
      change r.val*(r.val⁻¹*b.val*r.val)*r.val⁻¹ ∈ FourBlockResidual.H
      rw [show r.val*(r.val⁻¹*b.val*r.val)*r.val⁻¹=b.val by group]
      exact b.property.2
    refine ⟨⟨l.val,l.property,hlC⟩,?_⟩
    apply Subtype.ext
    change r.val*(q l).val*r.val⁻¹=b.val
    rw [hl]
    change r.val*(r.val⁻¹*b.val*r.val)*r.val⁻¹=b.val
    group
  refine ⟨r,f,hf,fun _ => rfl,?_⟩
  ext c
  change f c = 1 ↔ c.val ∈ L.pCoreIn 2
  have he : f c = 1 ↔ q (j c) = 1 := by
    constructor
    · intro hc
      apply Subtype.ext
      apply (MulAut.conj r.val).injective
      exact (congrArg Subtype.val hc).trans (map_one (MulAut.conj r.val)).symm
    · intro hc
      apply Subtype.ext
      change r.val*(q (j c)).val*r.val⁻¹=1
      rw [hc]
      change r.val*1*r.val⁻¹=1
      group
  rw [he]
  have hk : q (j c) = 1 ↔ j c ∈ pCore 2 L := by
    rw [←S.actionKernel_eq_core]
    change D.groupEquiv (QuotientGroup.mk' (conjugation L V S.chosen.normalizes).ker (j c)) = 1 ↔ _
    rw [←D.groupEquiv.map_one,D.groupEquiv.injective.eq_iff]
    exact QuotientGroup.eq_one_iff _
  rw [hk]
  constructor
  · exact mem_map_of_mem L.subtype
  · rintro ⟨l,hl,he⟩
    exact (show l = j c from Subtype.ext he) ▸ hl

/-- The point centralizer in L has three-rank two, via its literal quotient. -/
theorem SourceHypothesis.original_point_three_rank
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G)) :
    primeRank 3 (L ⊓ (D.fullSetup hZ T z).Gz : Subgroup G) = 2 := by
  obtain ⟨_,f,hf,_,hk⟩ := S.original_point_stabilizer_map D hZ z hz hTz
  have hp : IsPGroup 2 f.ker := hk ▸ (isPGroup_pCoreIn 2 L).comap_subtype
  have hc : Nat.Coprime 3 (Nat.card f.ker) := by
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  exact (primeRank_eq_of_surjective_of_coprime 3 f hf hc).trans FourBlockResidual.P_primeRank
end CFSG.Quasithin.Chapter12.Section06
