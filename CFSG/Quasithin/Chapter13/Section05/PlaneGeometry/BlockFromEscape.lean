module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.Source
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Stellmacher.BaumannNormalizer
public import Stellmacher.BaumannMap
public import Theory.GroupTheory.CharacteristicCentralizerSylow
/-!
# The unique maximal two-local application of C.1.24(c)

An escaping normalizer of the actual two-subgroup R rules out a nontrivial
characteristic subgroup of its Baumann subgroup that is normal in H. Indeed,
its ambient normalizer contains H and is controlled by the unique maximal
two-local overgroup, whereas it also contains the escaping normalizer of R.
Applying C.1.24(c) therefore yields the genuine alternating block.

Source: Aschbacher--Smith, 13.5.6, printed p.917. The unique maximal
two-local and normalizer escape are retained as the precise earlier-source
inputs; neither an alternating-block conclusion nor plane control is assumed.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin
namespace CFSG.Quasithin.Chapter13.Section05.PlaneGeometry
variable {G:Type*} [Group G] [Finite G]

theorem no_characteristic_baumann_normal_of_unique
    (H M:Subgroup G) (R:Subgroup H) (hp:IsPGroup 2 R)
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→H≤N→N=M)
    (he:¬normalizer (R.map H.subtype:Set G)≤M)
    (C:Subgroup (ChapterB.baumann R)) [C.Characteristic] (hn:C≠⊥) :
    ¬(C.map (ChapterB.baumann R).subtype).Normal := by
  intro hnormal
  let B:=ChapterB.baumann R
  let D:Subgroup G:=(C.map B.subtype).map H.subtype
  have hD:D≠⊥ := by
    intro hb
    exact hn ((C.map_eq_bot_iff_of_injective B.subtype_injective).mp
      (((C.map B.subtype).map_eq_bot_iff_of_injective H.subtype_injective).mp hb))
  have hDp:IsPGroup 2 D := (((hp.to_le inf_le_left).to_subgroup C).map B.subtype).map H.subtype
  have hHN:H≤normalizer (D:Set G) := by
    apply le_normalizer_iff.mpr
    intro h hh x hx
    obtain ⟨y,hy,rfl⟩:=hx
    exact mem_map_of_mem H.subtype (hnormal.conj_mem y hy ⟨h,hh⟩)
  have hN:normalizer (D:Set G)≤M := normalizer_le_of_unique_maximalTwoLocal hu hDp hD hHN
  apply he
  apply le_trans ?_ hN
  have hRB:normalizer (R.map H.subtype:Set G)≤normalizer (B.map H.subtype:Set G) := by
    have hb:B.map H.subtype=ChapterB.baumann (R.map H.subtype) := Stellmacher.baumann_map_injective H.subtype H.subtype_injective R
    rw [hb]
    exact Stellmacher.normalizer_le_normalizer_baumann _
  exact hRB.trans (normalizer_le_normalizer_characteristic_map H.subtype H.subtype_injective B C)
/-- The actual unique maximal two-local overgroup and the escaping Q₀
normalizer exclude the characteristic-normal branch of C.1.24(c). -/
theorem alternatingBlock_of_natural_six_and_unique
    (H M:Subgroup G) (L V R:Subgroup H)
    [V.Normal] [IsElementaryAbelian 2 V] [IsQuasisimple (L⧸pCore 2 L)]
    (hL:L.IsCComponent) (hf:generalizedFitting H=pCore 2 H)
    (hfL:generalizedFitting L=pCore 2 L)
    (T:Sylow 2 H) (hQR:pCore 2 H≤R) (hRT:R≤T)
    (hprod:∀g:H,∃l∈L,∃t∈(T:Subgroup H),l*t=g)
    (q:H→*Equiv.Perm (Fin 6)) (hLq:L.map q=alternatingGroup (Fin 6))
    (e:V≃*Multiplicative (BinaryPermutation.natural (Fin 6)))
    (he:∀(g:H)(v:V),(e (MulAut.conjNormal g v)).toAdd=
      BinaryPermutation.naturalRepresentation (Fin 6) (q g) (e v).toAdd)
    (hm:⁅V,L⁆≠⊥) (r:Equiv.Perm (Fin 6)) (hr:r.IsSwap) (hR:R.map q=zpowers r)
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→H≤N→N=M)
    (hescape:¬normalizer (R.map H.subtype:Set G)≤M) :
    ChapterC.IsAlternatingBlock L 6 := by
  rcases ChapterC.RankOne.SymmetricSix.normal_characteristic_or_alternatingBlock_of_natural_six
    L V R hL hf hfL T hQR hRT hprod q hLq e he hm r hr hR with ⟨C,hC,hCn,hCN⟩|hblock
  · let := hC
    exact (no_characteristic_baumann_normal_of_unique H M R (T.isPGroup'.to_le hRT)
      hu hescape C hCn hCN).elim
  · exact hblock

end CFSG.Quasithin.Chapter13.Section05.PlaneGeometry
