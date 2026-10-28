module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.TheoremA.Definitions
public import Theory.GroupTheory.SubgroupAutomorphismImages.Operations
public import Theory.GroupTheory.AutomorphismMaximumElementary

/-!
# The original maximum subgroup in Campbell II.7.3

A maximum elementary subgroup D of S whose outside conjugate centralizes
F^α modulo F must lie in O₂(H): otherwise D^g and J(S) generate J(H),
contrary to the chosen noncontainment. This applies to the literal
D=(B₀^g)^α. The remaining lemma collects the g-α-g word without extending
α to the ambient group.
Source: Campbell, Pushing up in Finite Groups, II.7.3, printed pp.34–35.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

 theorem InLocalClass.maximum_core_of_conjugate_commutator
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S)
    (M : Subgroup H) (hM : S ≤ M ∧ M ⋖ ⊤) (g : H) (hg : g ∉ M)
    (Y : Subgroup H) (hT : ⁅Campbell.J S,Y⁆ ≤ Campbell.F H)
    (hglobal : ¬ ⁅Campbell.J (⊤ : Subgroup H),Y⁆ ≤ Campbell.F H)
    (D : Subgroup H) (hD : D ∈ elementaryAbelianMaxSubgroups S)
    (hDY : ⁅D.map (MulAut.conj g).toMonoidHom,Y⁆ ≤ Campbell.F H) :
    D ≤ pCore 2 H := by
  by_contra hDQ
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  have hs : (d.sylow : Subgroup H)=S := hS.trans (range_subtype S)
  obtain ⟨n,hn,k,_,_,_,hk,⟨m⟩⟩ := h.natural
  let N := commutatorPreimage (⊤ : Subgroup H) Y (Campbell.F H)
  have hj : Campbell.J (⊤ : Subgroup H) ≤ N :=
    h.global_thompson_le_of_two_maxima hB m d hS D (hs.symm ▸ hD) hDQ M
      (by rw [hs];exact hM) g hg N
      (le_commutatorPreimage le_top (hs.symm ▸ hT))
      (le_commutatorPreimage le_top hDY)
  let : (Campbell.F H).Normal := Campbell.F_normal
  exact hglobal ((commutator_mono hj le_rfl).trans
    (commutator_commutatorPreimage_le ⊤ Y (Campbell.F H) le_normalizer_of_normal))

 theorem InLocalClass.double_conjugate_maximum_le_core_thompson
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S)
    (M : Subgroup H) (hM : S ≤ M ∧ M ⋖ ⊤) (g : H) (hg : g ∉ M)
    (a : MulAut S) (A : Subgroup H)
    (hA : A ∈ elementaryAbelianMaxSubgroups S) (hAQ : A ≤ pCore 2 H)
    (Y : Subgroup H) (hT : ⁅Campbell.J S,Y⁆ ≤ Campbell.F H)
    (hglobal : ¬ ⁅Campbell.J (⊤ : Subgroup H),Y⁆ ≤ Campbell.F H)
    (hDY : ⁅(automorphismImage S a (A.map (MulAut.conj g).toMonoidHom)).map
      (MulAut.conj g).toMonoidHom,Y⁆ ≤ Campbell.F H) :
    automorphismImage S a (A.map (MulAut.conj g).toMonoidHom) ≤ Campbell.J (pCore 2 H) := by
  obtain ⟨T,hT',_⟩ := h.sylow
  have hST : S=(T:Subgroup H) := (range_subtype S).symm.trans hT'
  have hc : A.map (MulAut.conj g).toMonoidHom ∈ elementaryAbelianMaxSubgroups S := by
    rw [hST] at hA ⊢
    exact maxElementary_conjugate_of_le_core T g A hA hAQ
  have ha := automorphismImage_maxElementary S a _ hc
  have hq := h.maximum_core_of_conjugate_commutator S hB M hM g hg Y hT hglobal _ ha hDY
  exact le_sSup ⟨hq,ha.2.1,fun C hc hce => ha.2.2 C
    (hc.trans (hST ▸ pCore_isPGroup.le_sylow_of_normal T)) hce⟩

namespace CampbellTheoremA
variable {H : Type*} [Group H]
 theorem conj_twice (g : H) (hg : g^2=1) (X : Subgroup H) :
    (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom=X := by
  rw [map_map]
  have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id H := by
    ext x
    have hi : g⁻¹=g := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hg)
    change g*(g*x*g⁻¹)*g⁻¹=x
    rw [hi]
    calc
      g*(g*x*g)*g = (g*g)*x*(g*g) := by group
      _ = x := by rw [←pow_two,hg];simp
  rw [he,Subgroup.map_id]

/-- Collect the literal g-a-g word in the first commutator argument. -/
theorem mixed_commutator_bound_transport (S : Subgroup H) (a : MulAut S)
    (g : H) (hg : g^2=1) (P Z : Subgroup H)
    (hPg : P.map (MulAut.conj g).toMonoidHom ≤ S)
    (hFg : (imageF S a).map (MulAut.conj g).toMonoidHom ≤ S) (hZS : Z ≤ S)
    (hc : ⁅P,mixedActor S a g⁆ ≤
      (automorphismImage S a.symm Z).map (MulAut.conj g).toMonoidHom) :
    ⁅(automorphismImage S a (P.map (MulAut.conj g).toMonoidHom)).map
      (MulAut.conj g).toMonoidHom,imageF S a⁆ ≤ Z.map (MulAut.conj g).toMonoidHom := by
  have h1 := map_mono (f := (MulAut.conj g).toMonoidHom) hc
  rw [map_commutator,show (mixedActor S a g).map (MulAut.conj g).toMonoidHom =
    automorphismImage S a.symm ((imageF S a).map (MulAut.conj g).toMonoidHom) from
    conj_twice g hg _,conj_twice g hg _] at h1
  have h2 := automorphismImage_mono S a h1
  rw [automorphismImage_commutator S a _ _ hPg (automorphismImage_le S a.symm _)] at h2
  have hF := automorphismImage_symm S a.symm _ hFg
  have hZ := automorphismImage_symm S a.symm Z hZS
  simp only [MulEquiv.symm_symm] at hF hZ
  rw [hF,hZ] at h2
  have h3 := map_mono (f := (MulAut.conj g).toMonoidHom) h2
  rwa [map_commutator,conj_twice g hg _] at h3

end CampbellTheoremA
end CFSG.Quasithin.ChapterC.GlaubermanNiles
