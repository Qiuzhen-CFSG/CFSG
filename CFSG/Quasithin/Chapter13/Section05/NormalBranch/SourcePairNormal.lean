module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairExact
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceStarBound
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.CubicNormalizer.SymmetricFactor
public import Theory.GroupTheory.PResidual.NormalizerImage
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Normality of the original symmetric-three pair

The original quaternion action places the pair image in the symmetric-three
factor of the cubic centralizer. That factor is normal in the full cubic
normalizer. Lifting first gives normality of I O₂(H), then of O²(I).
The source equality I=O²(I)V and H=L₁IT give normality of I itself.
The original chosen cubic, both module generators and the literal two-core
are retained throughout.

Source: Aschbacher–Smith, proof of13.5.15, printed p.920. The full cubic
centralizer is C₃×S₃; the pair is its S₃ factor, not the whole centralizer.
These conclusions feed the core elimination and uniqueness in13.5.15(6–7).
-/
@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairNormal
open Section08.SourceCompletion
open SourceOrthogonal SourceOrthogonalWitness SourceStarBound SourceOddRotation
open ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
  (hseed : D.Vplus=⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)

noncomputable def actor : D.H→*BinaryFourPlus.Wreath :=
  (starEmbedding d h e hseed hn hU).comp (QuotientGroup.mk' (pCore 2 D.H))

omit d h e hseed hn hU in
theorem pair_le (h : D.Hypothesis) {r:G} (hr:r∈D.H) :
    D.V⊔D.V.map (MulAut.conj r).toMonoidHom≤D.H :=
  sup_le h.V_le_H (by
    rintro _ ⟨v,hv,rfl⟩
    exact D.H.mul_mem (D.H.mul_mem hr (h.V_le_H hv)) (D.H.inv_mem hr))

theorem actor_range_normalizes :
    (actor d h e hseed hn hU).range≤normalizer (localCubic d h e hseed hn hU:Set BinaryFourPlus.Wreath) := by
  rintro _ ⟨x,rfl⟩
  exact range_normalizes_local d h e hseed hn hU ⟨_,rfl⟩

theorem module_image_centralizes :
    (D.V.subgroupOf D.H).map (actor d h e hseed hn hU)≤
      centralizer (localCubic d h e hseed hn hU:Set BinaryFourPlus.Wreath) := by
  rintro _ ⟨v,hv,rfl⟩
  exact module_actor_centralizes_local d h e hseed hn hU ⟨v.val,hv⟩

theorem pair_image_centralizes (r:G) (hr:r∈D.H) :
    ((D.V⊔D.V.map (MulAut.conj r).toMonoidHom).subgroupOf D.H).map
      (actor d h e hseed hn hU)≤
      centralizer (localCubic d h e hseed hn hU:Set BinaryFourPlus.Wreath) := by
  let α := actor d h e hseed hn hU
  let A := localCubic d h e hseed hn hU
  have hv := module_image_centralizes d h e hseed hn hU
  rw [subgroupOf_sup h.V_le_H (show D.V.map (MulAut.conj r).toMonoidHom≤D.H from
    le_sup_right.trans (pair_le h hr)),Subgroup.map_sup]
  refine sup_le hv ?_
  rintro _ ⟨x,⟨v,hvV,he⟩,rfl⟩
  let rH:D.H := ⟨r,hr⟩
  let vH:D.H := ⟨v,h.V_le_H hvV⟩
  have hx : x=rH*vH*rH⁻¹ := Subtype.ext he.symm
  rw [hx,map_mul,map_mul,map_inv]
  exact (mem_normalizer_iff.mp
    ((normalizer_le_normalizer_centralizer A) (actor_range_normalizes d h e hseed hn hU ⟨rH,rfl⟩))
    (α vH)).mp (hv (mem_map_of_mem α hvV))

theorem pair_image_eq_action_range (r:G) (hr:r∈D.H) :
    ((D.V⊔D.V.map (MulAut.conj r).toMonoidHom).subgroupOf D.H).map
      (actor d h e hseed hn hU)=
      (closureOrthogonalAction (D.V⊔D.V.map (MulAut.conj r).toMonoidHom)
        (pair_le h hr) (quaternion d h e hseed hn hU)).range := by
  let I := D.V⊔D.V.map (MulAut.conj r).toMonoidHom
  let α := actor d h e hseed hn hU
  have hc : α.comp (inclusion (pair_le h hr))=
      closureOrthogonalAction I (pair_le h hr) (quaternion d h e hseed hn hU) := rfl
  rw [←hc,MonoidHom.range_comp,inclusion_range]

theorem pair_image_structure (r:G) (hr:r∈D.H)
    (hj:Nonempty ((Section08.Source.starImage D.H
      (D.V⊔D.V.map (MulAut.conj r).toMonoidHom))≃*Equiv.Perm (Fin 3))) :
    let A:=localCubic d h e hseed hn hU
    let J:=((D.V⊔D.V.map (MulAut.conj r).toMonoidHom).subgroupOf D.H).map
      (actor d h e hseed hn hU)
    normalizer (A:Set BinaryFourPlus.Wreath)≤normalizer (J:Set BinaryFourPlus.Wreath) ∧
      centralizer (A:Set BinaryFourPlus.Wreath)=A⊔J ∧ Disjoint A J ∧ Nat.card (A⊔J:Subgroup BinaryFourPlus.Wreath)=18 := by
  dsimp only
  let I:=D.V⊔D.V.map (MulAut.conj r).toMonoidHom
  let A:=localCubic d h e hseed hn hU
  let J:=(I.subgroupOf D.H).map (actor d h e hseed hn hU)
  obtain ⟨_,hA,_,s,_,hs,_,hss,hc⟩:=exists_original_cubic_normalizer_witness d h e hseed hn hU
  have hJ:Nat.card J=6 := by
    change Nat.card ((I.subgroupOf D.H).map ((starEmbedding d h e hseed hn hU).comp
      (QuotientGroup.mk' (pCore 2 D.H))))=6
    rw [←map_map]
    rw [card_map_of_injective (starEmbedding_injective d h e hseed hn hU)]
    obtain ⟨f⟩:=hj
    change Nat.card (Section08.Source.starImage D.H I)=6
    rw [Nat.card_congr f.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  obtain ⟨a,b,ha,hb,_,_,he⟩:=h.closure_pair_orthogonal_generators (seed_index d)
    (module_not_le_core h hU) r hr (quaternion d h e hseed hn hU)
    (center_map d h e hseed hn hU) (pair_le h hr)
  apply BinaryFourPlus.CubicNormalizer.symmetric_factor_normalizer A J hA s hs hss hc
    (pair_image_centralizes d h e hseed hn hU r hr) hJ
  exact ⟨a,b,ha,hb,(pair_image_eq_action_range d h e hseed hn hU r hr).trans he⟩

include d h e hseed hn hU

/-- The selected pair together with the original local residual and Sylow
subgroup generates H; the quotient order bound is proved from its marked action. -/
theorem whole_generated (r:G) (hr:r∈D.H)
    (hj:Nonempty ((Section08.Source.starImage D.H
      (D.V⊔D.V.map (MulAut.conj r).toMonoidHom))≃*Equiv.Perm (Fin 3))) :
    D.H=D.L₁⊔(D.V⊔D.V.map (MulAut.conj r).toMonoidHom)⊔(D.T:Subgroup G) := by
  let I:=D.V⊔D.V.map (MulAut.conj r).toMonoidHom
  let Z:=D.L₁⊔I⊔(D.T:Subgroup G)
  let π:=QuotientGroup.mk' (pCore 2 D.H)
  let f:=starEmbedding d h e hseed hn hU
  let A:=localCubic d h e hseed hn hU
  let J:=(I.subgroupOf D.H).map (actor d h e hseed hn hU)
  let B:=Section08.Source.starImage D.H Z
  have hLH:D.L₁≤D.H:=le_sup_left.trans h.local_le
  have hIH:I≤D.H:=pair_le h hr
  have hZH:Z≤D.H:=sup_le (sup_le hLH hIH) h.T_le_H
  have hAB:A⊔J≤B.map f:=by
    apply sup_le
    · exact map_mono (map_mono (subgroupOf_mono D.H
        (show D.L₁≤Z from le_sup_left.trans le_sup_left)))
    · change (I.subgroupOf D.H).map (f.comp π)≤B.map f
      rw [←map_map]
      exact map_mono (map_mono (subgroupOf_mono D.H
        (show I≤Z from le_sup_right.trans le_sup_left)))
  have h18:18∣Nat.card B:=by
    have hd:=card_dvd_of_le hAB
    rw [(pair_image_structure d h e hseed hn hU r hr hj).2.2.2,
      card_map_of_injective (starEmbedding_injective d h e hseed hn hU)] at hd
    exact hd
  have hmul:18*B.index∣18*2:=
    (Nat.mul_dvd_mul_right h18 B.index).trans
      (B.card_mul_index ▸ original_star_card_dvd d h e hseed hn hU)
  have hi:B.index∣2:=Nat.dvd_of_mul_dvd_mul_left (by decide) hmul
  let S: Sylow 2 (Section08.Source.Hstar D.H):=
    (D.T.subtype h.T_le_H).mapSurjective (QuotientGroup.mk'_surjective _)
  have hSB:(S:Subgroup (Section08.Source.Hstar D.H))≤B:=by
    change ((D.T:Subgroup G).subgroupOf D.H).map π≤B
    exact map_mono (subgroupOf_mono D.H le_sup_right)
  have hodd:¬2∣B.index:=fun hd=>S.not_dvd_index (hd.trans (index_dvd_of_le hSB))
  have ht:B=⊤:=index_eq_one.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.prime_two.coprime_iff_not_dvd.mpr hodd) hi dvd_rfl)
  have he:=congrArg (Subgroup.comap π) ht
  change ((Z.subgroupOf D.H).map π).comap π=⊤ at he
  rw [comap_map_eq,QuotientGroup.ker_mk'] at he
  have hk:pCore 2 D.H≤Z.subgroupOf D.H:=by
    intro x hx
    exact (show (D.T:Subgroup G)≤Z from le_sup_right)
      (h.QH_le_T (mem_map_of_mem D.H.subtype hx))
  rw [sup_of_le_left hk] at he
  apply le_antisymm ?_ hZH
  intro x hx
  change (⟨x,hx⟩:D.H)∈Z.subgroupOf D.H
  rw [he]
  trivial

/-- The actual pair with the original two-core is normal in H. -/
theorem whole_normalizes_pair_core (r:G) (hr:r∈D.H)
    (hj:Nonempty ((Section08.Source.starImage D.H
      (D.V⊔D.V.map (MulAut.conj r).toMonoidHom))≃*Equiv.Perm (Fin 3))) :
    D.H≤normalizer ((D.V⊔D.V.map (MulAut.conj r).toMonoidHom⊔D.QH:Subgroup G):Set G) := by
  let I:=D.V⊔D.V.map (MulAut.conj r).toMonoidHom
  let α:=actor d h e hseed hn hU
  let J:=(I.subgroupOf D.H).map α
  have hk:α.ker=pCore 2 D.H:=by
    ext x
    change starEmbedding d h e hseed hn hU (QuotientGroup.mk' (pCore 2 D.H) x)=1↔_
    rw [show (1:BinaryFourPlus.Wreath)=starEmbedding d h e hseed hn hU 1 from
      (starEmbedding d h e hseed hn hU).map_one.symm,
      (starEmbedding_injective d h e hseed hn hU).eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hnorm:α.range≤normalizer (J:Set BinaryFourPlus.Wreath):=
    (actor_range_normalizes d h e hseed hn hU).trans
      (pair_image_structure d h e hseed hn hU r hr hj).1
  have hpre:(J.comap α).Normal:={
    conj_mem:=by
      intro x hx y
      change α (y*x*y⁻¹)∈J
      rw [map_mul,map_mul,map_inv]
      exact (mem_normalizer_iff.mp (hnorm ⟨y,rfl⟩) (α x)).mp hx }
  have he:(J.comap α).map D.H.subtype=I⊔D.QH:=by
    rw [comap_map_eq,hk,Subgroup.map_sup,map_subgroupOf_eq_of_le (pair_le h hr)]
    rfl
  rw [←he]
  let := hpre
  simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
    (J.comap α).le_normalizer_map D.H.subtype

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairNormal
end
