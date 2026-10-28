module

public import CFSG.Quasithin.Chapter13.Section07.PairQuotient
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreGeneration

/-!
# The original paired spans and local core generate modulo O₂(LT)

The actual image of O₂(H) is the full natural-point core. The two span
images contain the point transposition and its noncommuting conjugate.
The native six-letter generation theorem therefore gives the entire
quotient S₆. Lifting through the already identified action kernel proves
LT = ⟨V_H,V_H^g,O₂(H)⟩ O₂(LT), with the literal source subgroups.

This is the generation step in Aschbacher–Smith 13.7.17, printed p.944.
Only original F.9 applicability, abelian seed span, the contrary
nonabelian full span, and earlier point-core noncentrality are inputs.
-/

@[expose] public section
open Subgroup BinaryPermutation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion NaturalAction ChapterF.Section09.Setup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
variable {G:Type*} [Group G] [Finite G]
  {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- Source 13.7.17 generation on the actual chosen pair, before using any
component or module classification. -/
theorem pair_core_generate
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (hne:⁅V₃,Section08.Source.QH H⁆≠⊥)
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let I:=Section08.Source.VH H V⊔conjugate (Section08.Source.VH H V) (g:G)
    (I⊔Section08.Source.QH H)⊔(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2=
      L⊔(T:Subgroup G) := by
  dsimp only
  let X:=L⊔(T:Subgroup G)
  let A:=Section08.Source.VH H V
  let B:=conjugate A (g:G)
  let I:=A⊔B
  let J:=I⊔Section08.Source.QH H
  let Q:=X.pCoreIn 2
  let π:=permutation d
  let P:=image d V₁
  have hQHX:Section08.Source.QH H≤X:=h.QH_le_T.trans le_sup_right
  have hAX:A≤X:=(VH_le_core d h hU).trans hQHX
  have hBX:B≤X := by
    rintro _ ⟨a,ha,rfl⟩
    change (g:G)⁻¹*a*((g:G)⁻¹)⁻¹∈X
    rw [inv_inv]
    exact X.mul_mem (X.mul_mem (X.inv_mem g.property) (hAX ha)) g.property
  have hJX:J≤X:=sup_le (sup_le hAX hBX) hQHX
  have hpoint:V₁≤V:=h.point_lt.le.trans h.plus_le
  have hPdim:Module.finrank (ZMod 2) P=1:=image_dim d V₁ hpoint 1 d.line_card
  have hPgV:conjugate V₁ (g:G)≤V := by
    have hv:conjugate V (g:G)=V:=mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (V:Set G)).inv_mem (d.normalizes_V g.property))
    exact (map_mono hpoint).trans hv.le
  obtain ⟨t,ht,htA,_⟩:=nonabelian_transposition_images d h hU hV
  have htmem:t∈(A.subgroupOf X).map π:=htA.symm ▸ mem_zpowers t
  obtain ⟨a,ha,hat⟩:=htmem
  have htf:∀w∈form.orthogonal P,naturalRepresentation (Fin 6) t w=w := by
    intro w hw
    rw [←seed_perpendicular d] at hw
    obtain ⟨v,hv,rfl⟩:=(mem_image d V₃ _).mp hw
    rw [←hat,←conjugation d a v]
    apply congrArg (fun b:V=>(d.coordinate b).toAdd)
    apply Subtype.ext
    have hc: a.val∈centralizer (V₃:Set G):=
      (centralizer_le (le_conjugateSpanBy V₃ H)) ((VH_centralizes_UH d h hU) ha).2
    change a.val*v.val*a.val⁻¹=v.val
    rw [←hc v.val hv,mul_inv_cancel_right]
  have hcross:¬P.map (naturalRepresentation (Fin 6) (π g)⁻¹)≤form.orthogonal P := by
    intro hc
    have him:image d (conjugate V₁ (g:G))≤ image d V₃ := by
      rw [natural_image_conjugate d V₁ hpoint,seed_perpendicular d,map_inv]
      exact hc
    apply hout
    intro x hx
    have hh:=him ((mem_image d _ _).mpr ⟨⟨x,hPgV hx⟩,hx,rfl⟩)
    obtain ⟨v,hv,he⟩:=(mem_image d V₃ _).mp hh
    have hvx:v=(⟨x,hPgV hx⟩:V):=d.coordinate.injective he
    have hev:v.val=x:=congrArg Subtype.val hvx
    have hv':x∈V₃:=hev ▸ hv
    exact le_conjugateSpanBy V₃ H hv'
  let s:Equiv.Perm (Fin 6):=(π g)⁻¹*t*((π g)⁻¹)⁻¹
  have hs:s.IsSwap := by
    obtain ⟨i,j,hij,rfl⟩:=ht
    rw [show s=Equiv.swap ((π g)⁻¹ i) ((π g)⁻¹ j) from (Equiv.swap_apply_apply _ _ _).symm]
    exact ⟨_,_,(π g).symm.injective.ne hij,rfl⟩
  have hnecomm:¬Commute t s:=
    Theory.SpecificGroups.SymmetricSix.BinaryFlags.TransvectionPair.not_commute P
      (P.map (naturalRepresentation (Fin 6) (π g)⁻¹)) hPdim
      ((LinearMap.GeneralLinearGroup.toLinearEquiv
        ((naturalRepresentation (Fin 6)).asGroupHom (π g)⁻¹)).finrank_map_eq P |>.trans hPdim)
      t s (by intro he; have hh:=ht.orderOf; rw [he,orderOf_one] at hh; contradiction) (by intro he; have hh:=hs.orderOf; rw [he,orderOf_one] at hh; contradiction) htf
      (Theory.SpecificGroups.SymmetricSix.BinaryFlags.TransvectionPair.conjugate_fixes P (π g)⁻¹ t htf) hcross
  have hcore:((Section08.Source.QH H).subgroupOf X).map π=
      (subspaceStabilizer (naturalRepresentation (Fin 6)) P).pCoreIn 2:=
    nonabelian_core_image d h hU hV hne
  have htcore:t∈(subspaceStabilizer (naturalRepresentation (Fin 6)) P).pCoreIn 2 := by
    rw [←hcore]
    exact ⟨a,VH_le_core d h hU ha,hat⟩
  have hfull:=Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreGeneration.point_core_generate
    P hPdim t s ht hs htcore hnecomm
  have hjimage:(J.subgroupOf X).map π=⊤ := by
    apply top_unique
    rw [←hfull]
    refine sup_le ?_ (zpowers_le.mpr ?_)
    · rw [←hcore]
      exact map_mono (comap_mono le_sup_right)
    · refine ⟨g⁻¹*a*g,?_,?_⟩
      · apply mem_sup_left
        apply mem_sup_right
        exact ⟨a.val,ha,by change (g:G)⁻¹*a.val*((g:G)⁻¹)⁻¹=(g:G)⁻¹*a.val*(g:G); rw [inv_inv]⟩
      · simp only [map_mul,map_inv,hat,s,inv_inv]
  apply le_antisymm (sup_le hJX (pCoreIn_le 2 X))
  intro x hx
  have him:π ⟨x,hx⟩∈(J.subgroupOf X).map π:=hjimage.symm ▸ mem_top _
  obtain ⟨y,hy,he⟩:=him
  have hk:(⟨x,hx⟩:X)*y⁻¹∈pCore 2 X := by
    rw [←nonabelian_permutation_kernel d h hU hV]
    change π ((⟨x,hx⟩:X)*y⁻¹)=1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hxy:x*y.val⁻¹∈Q:=mem_map_of_mem X.subtype hk
  have hh:=(J⊔Q).mul_mem (mem_sup_right hxy) (mem_sup_left hy)
  change (x*y.val⁻¹)*y.val∈J⊔Q at hh
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh

/-- The generation formula for the source-constructed square-marked conjugator. -/
theorem exists_source_pair_core_generate
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (hHG:H≤G₁) (hne:⁅V₃,G₁.pCoreIn 2⁆≠⊥) :
    ∃g:L,
      (QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) (inclusion le_sup_left g))^2=1 ∧
      V≤V₃⊔conjugate V₁ (g:G) ∧
      ¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃ ∧
      ((Section08.Source.VH H V⊔conjugate (Section08.Source.VH H V) (g:G))⊔Section08.Source.QH H)⊔
        (L⊔(T:Subgroup G):Subgroup G).pCoreIn 2=L⊔(T:Subgroup G) := by
  obtain ⟨g,hs,hspan⟩:=exists_chosen_conjugator d
  have hout:=ConjugateIntersections.lemma_13_7_10_one h (g:G) hspan hU hV
  exact ⟨g,hs,hspan,hout,pair_core_generate d h hU hV
    (seed_noncentral_on_local_core h hHG hne) (inclusion le_sup_left g) hout⟩

end CFSG.Quasithin.Chapter13.Section07
