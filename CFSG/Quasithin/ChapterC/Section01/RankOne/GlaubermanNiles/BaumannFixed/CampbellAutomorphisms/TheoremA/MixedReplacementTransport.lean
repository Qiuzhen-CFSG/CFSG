module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.TheoremA.FirstReplacement
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.TheoremA.WordControl

/-!
# Campbell II.7.6: the mixed maximum replacement and commutator

Transport the actual second replacement B through g followed by α.
Its image D is maximum elementary and contains F, hence centralizes F;
the source point-centralizer theorem puts D in O₂(H). The conjugate
replacement and dichotomy for F^(αg) now apply to D. Pulling back through
α⁻¹ and g gives the maximum replacement Y C_B(Y) and commutator values
1 or Z^g, for Y=F^(αgα⁻¹g). No automorphism of the ambient group extending
α is used. The returned core containment is for the original subgroups.
Source: Campbell, Pushing up in Finite Groups, II.7.6, printed p.35.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
open CampbellTheoremA
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

omit [Finite H] in
private theorem conj_relative_centralizer (g : H) (B Y : Subgroup H) :
    (B ⊓ centralizer (Y : Set H)).map (MulAut.conj g).toMonoidHom =
      B.map (MulAut.conj g).toMonoidHom ⊓ centralizer (Y.map (MulAut.conj g).toMonoidHom : Set H) := by
  apply le_antisymm
  · exact le_inf (map_mono inf_le_left) ((map_mono inf_le_right).trans
      (map_centralizer_le_centralizer_image _ _))
  · rintro x ⟨⟨b,hb,rfl⟩,hc⟩
    refine ⟨b,⟨hb,?_⟩,rfl⟩
    intro y hy
    apply (MulAut.conj g).injective
    exact map_mul (MulAut.conj g) y b ▸ map_mul (MulAut.conj g) b y ▸
      hc ((MulAut.conj g) y) (mem_map_of_mem (MulAut.conj g).toMonoidHom hy)

private theorem transported_replacement_core
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S) (a : MulAut S)
    (g : H) (hg2 : g^2=1) (B : Subgroup H)
    (hb : B ∈ elementaryAbelianMaxSubgroups S) (hbQ : B ≤ pCore 2 H)
    (hFB : inverseConjugate S a g ≤ B) :
    automorphismImage S a (B.map (MulAut.conj g).toMonoidHom) ∈ elementaryAbelianMaxSubgroups S ∧
      automorphismImage S a (B.map (MulAut.conj g).toMonoidHom) ≤ pCore 2 H := by
  obtain ⟨T,hT,_⟩ := h.sylow
  have hST : S=(T:Subgroup H) := (range_subtype S).symm.trans hT
  have hQS : pCore 2 H ≤ S := hST ▸ pCore_isPGroup.le_sylow_of_normal T
  have hbg : B.map (MulAut.conj g).toMonoidHom ∈ elementaryAbelianMaxSubgroups S := by
    rw [hST]
    exact maxElementary_conjugate_of_le_core T g B (hST ▸ hb) hbQ
  have hd := automorphismImage_maxElementary S a _ hbg
  have hFi := map_mono (f := (MulAut.conj g).toMonoidHom) hFB
  change ((imageF S a.symm).map (MulAut.conj g).toMonoidHom).map
    (MulAut.conj g).toMonoidHom ≤ _ at hFi
  rw [conj_twice g hg2] at hFi
  have hF := automorphismImage_mono S a hFi
  have hround := automorphismImage_symm S a.symm (Campbell.F H) (Campbell.F_le_pCore.trans hQS)
  simp only [MulEquiv.symm_symm] at hround
  change automorphismImage S a (automorphismImage S a.symm (Campbell.F H)) ≤ _ at hF
  rw [hround] at hF
  let D := automorphismImage S a (B.map (MulAut.conj g).toMonoidHom)
  let : IsElementaryAbelian 2 D := hd.2.1
  have hDC : D ≤ centralizer (Campbell.F H : Set H) :=
    (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hF)
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  obtain ⟨n,hn,k,_,_,_,hk,⟨m⟩⟩ := h.natural
  have hs : (d.sylow : Subgroup H)=S := hS.trans (range_subtype S)
  refine ⟨hd,(le_inf hd.1 hDC).trans ?_⟩
  rw [←hs]
  exact h.sylow_centralizer_campbellF_le_core hB m d

theorem InLocalClass.mixed_replacement_maximum_and_commutator
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S) (a : MulAut S)
    (hAll : ∀ b : MulAut S, automorphismImage S b (Campbell.V H) ≤ pCore 2 H)
    (hF : ¬imageF S a ≤ Campbell.F H)
    (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (g : H) (hgK : g ∈ Campbell.J (⊤ : Subgroup H)) (hg2 : g^2=1) :
    (mixedActor S a g ⊔ (replacement S a A g ⊓ centralizer (mixedActor S a g : Set H))) ∈
      elementaryAbelianMaxSubgroups S ∧
    mixedActor S a g ⊔ (replacement S a A g ⊓ centralizer (mixedActor S a g : Set H)) ≤ pCore 2 H ∧
    (⁅replacement S a A g,mixedActor S a g⁆=⊥ ∨
      ⁅replacement S a A g,mixedActor S a g⁆=(fixed S).map (MulAut.conj g).toMonoidHom) := by
  let B := replacement S a A g
  let D := automorphismImage S a (B.map (MulAut.conj g).toMonoidHom)
  let Fag := (imageF S a).map (MulAut.conj g).toMonoidHom
  let W := automorphismImage S a.symm Fag
  have hb := h.replacement_geometry S hB a hAll A hA g
  have hd := transported_replacement_core S h hB a g hg2 B hb.1 hb.2.1 le_sup_left
  obtain ⟨T,hT,_⟩ := h.sylow
  have hST : S=(T:Subgroup H) := (range_subtype S).symm.trans hT
  have hQS : pCore 2 H ≤ S := hST ▸ pCore_isPGroup.le_sylow_of_normal T
  have hbgQ : B.map (MulAut.conj g).toMonoidHom ≤ pCore 2 H := by
    rintro x ⟨b,hb',rfl⟩
    exact (inferInstance : (pCore 2 H).Normal).conj_mem b (hb.2.1 hb') g
  have hbgS := hbgQ.trans hQS
  have hDi : automorphismImage S a.symm D=B.map (MulAut.conj g).toMonoidHom :=
    automorphismImage_symm S a _ hbgS
  have hFgS : Fag ≤ S := by
    obtain ⟨E,he,_,hfe⟩ := h.automorphism_F_conjugate_submaximal S hB a (hAll a) g
    exact hfe.trans he.1
  have hgo : ∃ n, orderOf g=2^n := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hg2) with ho | ho
    · exact ⟨0,by simpa using ho⟩
    · exact ⟨1,by simpa using ho⟩
  have hwQ : W ≤ pCore 2 H := h.inverse_conjugate_core S hB a (hAll a) g hgK hgo
  have hyQ : mixedActor S a g ≤ pCore 2 H := by
    rintro x ⟨w,hw,rfl⟩
    exact (inferInstance : (pCore 2 H).Normal).conj_mem w (hwQ hw) g
  have hr := h.automorphism_conjugate_replacement S hB a (hAll a) D hd.1 hd.2 g
  have hi := automorphismImage_maxElementary S a.symm _ hr
  change automorphismImage S a.symm (Fag ⊔ (D ⊓ centralizer (Fag : Set H))) ∈ _ at hi
  rw [automorphismImage_sup S a.symm _ _ hFgS (inf_le_left.trans hd.1.1),
    automorphismImage_inf_centralizer S a.symm _ _ hFgS,hDi] at hi
  have hiQ : W ⊔ (B.map (MulAut.conj g).toMonoidHom ⊓ centralizer (W : Set H)) ≤ pCore 2 H :=
    sup_le hwQ (inf_le_left.trans hbgQ)
  have hmax := maxElementary_conjugate_of_le_core T g _ (hST ▸ hi) hiQ
  rw [Subgroup.map_sup,conj_relative_centralizer,conj_twice g hg2] at hmax
  rw [←hST] at hmax
  refine ⟨hmax,sup_le hyQ (inf_le_left.trans hb.2.1),?_⟩
  have hZaC := h.automorphism_fixed_le_center S hB a (hAll a) hF
  have hZag : (automorphismImage S a (fixed S)).map (MulAut.conj g).toMonoidHom =
      automorphismImage S a (fixed S) := by
    apply le_antisymm
    · rintro x ⟨z,hz,rfl⟩
      change g*z*g⁻¹ ∈ automorphismImage S a (fixed S)
      rw [mem_center_iff.mp (hZaC hz) g,mul_inv_cancel_right]
      exact hz
    · intro z hz
      refine ⟨z,hz,?_⟩
      change g*z*g⁻¹=z
      rw [mem_center_iff.mp (hZaC hz) g,mul_inv_cancel_right]
  have hZS : fixed S ≤ S := (inf_le_left.trans Campbell.V_le_pCore).trans hQS
  rcases h.automorphism_conjugate_commutator_dichotomy S hB a D hd.1 hd.2 g with hzero | hvalue
  · change ⁅D,Fag⁆=⊥ at hzero
    have he := congrArg (automorphismImage S a.symm) hzero
    rw [automorphismImage_commutator S a.symm D Fag hd.1.1 hFgS,hDi,automorphismImage_bot] at he
    have he' := congrArg (fun E : Subgroup H => E.map (MulAut.conj g).toMonoidHom) he
    rw [map_commutator,conj_twice g hg2,Subgroup.map_bot] at he'
    exact Or.inl he'
  · change ⁅D,Fag⁆=(automorphismImage S a (fixed S)).map (MulAut.conj g).toMonoidHom at hvalue
    rw [hZag] at hvalue
    have he := congrArg (automorphismImage S a.symm) hvalue
    rw [automorphismImage_commutator S a.symm D Fag hd.1.1 hFgS,hDi,
      automorphismImage_symm S a (fixed S) hZS] at he
    have he' := congrArg (fun E : Subgroup H => E.map (MulAut.conj g).toMonoidHom) he
    rw [map_commutator,conj_twice g hg2] at he'
    exact Or.inr he'
end CFSG.Quasithin.ChapterC.GlaubermanNiles
