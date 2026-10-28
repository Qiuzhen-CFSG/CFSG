module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.TheoremA.Definitions

/-!
# Actual automorphism replacements and commutator alternatives

Maximum elementary replacement and its two commutator values transport
through the literal Sylow automorphism and conjugation inside the two-core.
These are the replacement inputs for Campbell II.7.2–6, pp.33–35.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

theorem InLocalClass.automorphism_F_replacement (h : InLocalClass S.subtype)
    (hB : IsBaumannFixed S) (a : MulAut S) (A : Subgroup H)
    (hA : A ∈ elementaryAbelianMaxSubgroups S) :
    automorphismImage S a (Campbell.F H) ⊔
      (A ⊓ centralizer (automorphismImage S a (Campbell.F H) : Set H)) ∈
        elementaryAbelianMaxSubgroups S := by
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  have hSd : (d.sylow : Subgroup H)=S := hS.trans (range_subtype S)
  obtain ⟨n,hn,k,_,_,_,hk,⟨m⟩⟩ := h.natural
  have hFQ : Campbell.F H ≤ S := Campbell.F_le_pCore.trans
    (hSd ▸ pCore_isPGroup.le_sylow_of_normal d.sylow)
  have hAi := automorphismImage_maxElementary S a.symm A hA
  have hr := h.campbellF_centralizer_replacement hB m d (automorphismImage S a.symm A) (hSd.symm ▸ hAi)
  have hm := automorphismImage_maxElementary S a _ (hSd ▸ hr)
  rw [automorphismImage_sup S a _ _ hFQ
      (inf_le_left.trans (automorphismImage_le S a.symm A)),
    automorphismImage_inf_centralizer S a _ _ hFQ] at hm
  have hid : automorphismImage S a (automorphismImage S a.symm A)=A := by
    simpa only [MulEquiv.symm_symm] using automorphismImage_symm S a.symm A hA.1
  rwa [hid] at hm

theorem InLocalClass.automorphism_F_commutator_dichotomy (h : InLocalClass S.subtype)
    (hB : IsBaumannFixed S) (a : MulAut S) (A : Subgroup H)
    (hA : A ∈ elementaryAbelianMaxSubgroups S) :
    ⁅A,automorphismImage S a (Campbell.F H)⁆=⊥ ∨
      ⁅A,automorphismImage S a (Campbell.F H)⁆=
        automorphismImage S a (Campbell.V H ⊓ centralizer (S : Set H)) := by
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  have hSd : (d.sylow : Subgroup H)=S := hS.trans (range_subtype S)
  have hSdSet : (d.sylow : Set H)=(S : Set H) := congrArg (fun X : Subgroup H => (X : Set H)) hSd
  obtain ⟨n,hn,k,_,_,_,hk,⟨m⟩⟩ := h.natural
  have hFS : Campbell.F H ≤ S := Campbell.F_le_pCore.trans
    (hSd ▸ pCore_isPGroup.le_sylow_of_normal d.sylow)
  have hAi := automorphismImage_maxElementary S a.symm A hA
  have hid : automorphismImage S a (automorphismImage S a.symm A)=A := by
    simpa only [MulEquiv.symm_symm] using automorphismImage_symm S a.symm A hA.1
  rcases h.campbellF_commutator_dichotomy hB m d hS _ (by rw [hSd]; exact hAi) with hb | he
  · have hi := congrArg (automorphismImage S a) hb
    rw [automorphismImage_commutator S a _ _ (automorphismImage_le S a.symm A) hFS,
      hid,automorphismImage_bot] at hi
    exact Or.inl hi
  · have hi := congrArg (automorphismImage S a) he
    rw [automorphismImage_commutator S a _ _ (automorphismImage_le S a.symm A) hFS,hid,hSdSet] at hi
    exact Or.inr hi

omit [Finite H] in
private theorem conj_roundtrip (g : H) (A : Subgroup H) :
    (A.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom=A := by
  rw [Subgroup.map_map]
  have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom=MonoidHom.id H := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  rw [he,Subgroup.map_id]

omit [Finite H] in
private theorem conj_inf_centralizer (g : H) (A Y : Subgroup H) :
    (A ⊓ centralizer (Y : Set H)).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj g).toMonoidHom ⊓ centralizer (Y.map (MulAut.conj g).toMonoidHom : Set H) := by
  apply le_antisymm
  · exact le_inf (map_mono inf_le_left) ((map_mono inf_le_right).trans (map_centralizer_le_centralizer_image _ _))
  · rintro x ⟨⟨a,ha,rfl⟩,hc⟩
    refine ⟨a,⟨ha,?_⟩,rfl⟩
    intro y hy
    apply (MulAut.conj g).injective
    exact map_mul (MulAut.conj g) y a ▸ map_mul (MulAut.conj g) a y ▸
      hc ((MulAut.conj g) y) (mem_map_of_mem (MulAut.conj g).toMonoidHom hy)

theorem InLocalClass.automorphism_conjugate_replacement (h : InLocalClass S.subtype)
    (hB : IsBaumannFixed S) (a : MulAut S)
    (hV : automorphismImage S a (Campbell.V H) ≤ pCore 2 H)
    (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups S) (hAQ : A ≤ pCore 2 H) (g : H) :
    (automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom ⊔
      (A ⊓ centralizer ((automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom : Set H)) ∈
        elementaryAbelianMaxSubgroups S := by
  obtain ⟨T,hT,_⟩ := h.sylow
  have hST : S=(T:Subgroup H) := (range_subtype S).symm.trans hT
  have hAi : A.map (MulAut.conj g⁻¹).toMonoidHom ∈ elementaryAbelianMaxSubgroups S := by
    simpa only [←hST] using maxElementary_conjugate_of_le_core T g⁻¹ A (hST ▸ hA) hAQ
  have hr := h.automorphism_F_replacement S hB a _ hAi
  have hYQ : automorphismImage S a (Campbell.F H) ≤ pCore 2 H :=
    (le_conjugateSpanBy _ _).trans (h.sylow_automorphism_span S hB a hV).1
  have hArQ : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ pCore 2 H := by
    rintro x ⟨y,hy,rfl⟩
    exact (inferInstance : (pCore 2 H).Normal).conj_mem y (hAQ hy) g⁻¹
  have hRQ : automorphismImage S a (Campbell.F H) ⊔
      (A.map (MulAut.conj g⁻¹).toMonoidHom ⊓ centralizer (automorphismImage S a (Campbell.F H) : Set H)) ≤ pCore 2 H :=
    sup_le hYQ (inf_le_left.trans hArQ)
  have hm := maxElementary_conjugate_of_le_core T g _ (hST ▸ hr) hRQ
  rw [Subgroup.map_sup,conj_inf_centralizer,conj_roundtrip] at hm
  simpa only [←hST] using hm

theorem InLocalClass.automorphism_conjugate_commutator_dichotomy (h : InLocalClass S.subtype)
    (hB : IsBaumannFixed S) (a : MulAut S)
    (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups S) (hAQ : A ≤ pCore 2 H) (g : H) :
    ⁅A,(automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom⁆=⊥ ∨
      ⁅A,(automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom⁆=
        (automorphismImage S a (Campbell.V H ⊓ centralizer (S : Set H))).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨T,hT,_⟩ := h.sylow
  have hST : S=(T:Subgroup H) := (range_subtype S).symm.trans hT
  have hAi : A.map (MulAut.conj g⁻¹).toMonoidHom ∈ elementaryAbelianMaxSubgroups S := by
    simpa only [←hST] using maxElementary_conjugate_of_le_core T g⁻¹ A (hST ▸ hA) hAQ
  rcases h.automorphism_F_commutator_dichotomy S hB a _ hAi with hb | he
  · have hi := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hb
    rw [map_commutator,conj_roundtrip,Subgroup.map_bot] at hi
    exact Or.inl hi
  · have hi := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) he
    rw [map_commutator,conj_roundtrip] at hi
    exact Or.inr hi
end CFSG.Quasithin.ChapterC.GlaubermanNiles
