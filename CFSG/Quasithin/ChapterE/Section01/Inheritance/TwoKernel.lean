module

public import CFSG.Quasithin.ChapterE.Section01.ReverseLift.Preparation
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.OddSections.Common
public import Theory.GroupTheory.PCoreSurjective

/-!
# Odd E-members under a two-group kernel

The full preimage preserves an odd E-member through a surjection with
2-group kernel. Its intrinsic quotient by the two-core is unchanged.
The original actor, ambient tau condition, and prescribed Sylow intersection
all lift directly. Consequently the whole image, the odd alternative, and
escape from a marked subgroup are retained without shrinking the member.

Source application: Aschbacher–Smith E.1.10(7), E.1.11 and E.2.2,
printed pp.211–216.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterE
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

theorem ECaseOdd.comap_of_two_kernel (f : G →* H) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (A : Subgroup G) (I : Subgroup H)
    (ho : ECaseOdd (A.map f) I) : ECaseOdd A (I.comap f) := by
  let P := I.comap f
  let g : P →* I := (f.comp P.subtype).codRestrict I (fun x => x.property)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x,hx⟩ := hf y
    exact ⟨⟨x,by change f x∈I; rw [hx]; exact y.property⟩,Subtype.ext hx⟩
  have hkg : IsPGroup 2 g.ker := by
    have he : g.ker = f.ker.subgroupOf P := by
      ext x
      change g x=1 ↔ f x=1
      exact Subtype.ext_iff
    rw [he]
    exact hk.comap_subtype
  let q := (QuotientGroup.mk' (pCore 2 I)).comp g
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp hg
  have hqk : q.ker = pCore 2 P := by
    have he : q.ker = (pCore 2 I).comap g := by
      ext x
      exact QuotientGroup.eq_one_iff _
    exact he.trans (g.comap_pCore_of_ker_isPGroup hg hkg)
  have hA : (A.subgroupOf P).map g = (A.map f).subgroupOf I := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact mem_map_of_mem f hx
    · rintro ⟨x,hx,he⟩
      exact ⟨⟨x,by change f x∈I; rw [he]; exact y.property⟩,hx,Subtype.ext he⟩
  obtain ⟨p,hp,hpo,hquot,hne,hcomm,hrank⟩ := ho
  refine ⟨p,hp,hpo,?_⟩
  apply ValuesOdd.PSLTwoGeneration.PrimeGeometry.OddSections.intrinsic_of_epimorphism
    (A.subgroupOf P) q hq hqk
  have hm : (A.subgroupOf P).map q = ((A.map f).subgroupOf I).map
      (QuotientGroup.mk' (pCore 2 I)) := by
    change (A.subgroupOf P).map ((QuotientGroup.mk' (pCore 2 I)).comp g) = _
    rw [←map_map,hA]
  exact ⟨hquot,hne,by rw [hm]; exact hcomm,(Subgroup.rank_congr hm).trans hrank⟩

theorem odd_eMember_comap_of_two_kernel (T : Sylow 2 G) (A : Subgroup G)
    [IsElementaryAbelian 2 A] (hAT : A≤T)
    (f : G →* H) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (I : Subgroup H) (hI : IsEMemberAt 1 ((T : Subgroup G).map f) (A.map f) I)
    (ho : ECaseOdd (A.map f) I) :
    IsEMemberAt 1 (T : Subgroup G) A (I.comap f) ∧ ECaseOdd A (I.comap f) := by
  have hAP : A≤I.comap f := map_le_iff_le_comap.mp hI.1.2.2.1
  have htau : tau (T : Subgroup G) A ≤ I.comap f := map_le_iff_le_comap.mp
    ((map_tau_le_of_surjective f hf _ _).trans (hI.1.2.2.2.1.trans inf_le_right))
  obtain ⟨S,hS⟩ := hI.1.2.2.2.2.1
  have hs := T.exists_subgroupOf_eq_comap f I S hS
  have hu := ho.comap_of_two_kernel f hf hk A I
  have hrank : Group.rank ((A.subgroupOf (I.comap f)).map
      (QuotientGroup.mk' (pCore 2 (I.comap f))))=1 := by
    obtain ⟨p,_,_,_,_,_,hr⟩ := hu
    exact hr
  exact ⟨⟨⟨inferInstance,hAT,hAP,le_inf (tau_le _ _) htau,hs,Or.inl hu⟩,
    Or.inl ⟨hu,hrank.le⟩⟩,hu⟩

theorem odd_escape_comap_of_two_kernel (T : Sylow 2 G) (A : Subgroup G)
    [IsElementaryAbelian 2 A] (hAT : A≤T)
    (f : G →* H) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (M : Subgroup G) (I : Subgroup H)
    (hI : IsEMemberAt 1 ((T : Subgroup G).map f) (A.map f) I)
    (ho : ECaseOdd (A.map f) I) (hIM : ¬ I≤M.map f) :
    IsEMemberAt 1 (T : Subgroup G) A (I.comap f) ∧ ECaseOdd A (I.comap f) ∧
      ¬I.comap f≤M := by
  obtain ⟨hm,ho⟩ := odd_eMember_comap_of_two_kernel T A hAT f hf hk I hI ho
  refine ⟨hm,ho,fun h => hIM ?_⟩
  have he := map_mono (f:=f) h
  rwa [map_comap_eq_self_of_surjective hf] at he

end CFSG.Quasithin.ChapterE
