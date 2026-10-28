module
public import Theory.GroupTheory.PairNormalizerIndex
public import Theory.GroupTheory.SylowPreimageNormalizer
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.AutomorphismMaximumElementary
/-!
# The Frattini endgame for two invariant maximum elementary subgroups

If the common normalizer of S and R permutes only two maximum elementary
subgroups of S, and an ambient Sylow subgroup fixes one of them, the whole
common normalizer fixes it: a moved pair would give index two, contradicting
Sylow index. The literal Sylow intersection with the preimage of a normal
two-subgroup supplies the complementary Frattini generation theorem.

These are the final group-theoretic steps in Aschbacher–Smith 10.2.1,
printed p.743. The finite four-factor geometry supplies the two-member
maximum family; it is not replaced by a desired normalizer hypothesis.
-/
public section
open Subgroup Stellmacher
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
theorem le_normalizer_of_sylow_fixed_pair
    (T : Sylow 2 G) (H V A : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hpair : ∀ h ∈ H, V.map (MulAut.conj h).toMonoidHom = V ∨
      V.map (MulAut.conj h).toMonoidHom = A) :
    H ≤ normalizer (V : Set G) := by
  by_contra hn
  obtain ⟨x,hx,hxn⟩ := SetLike.not_le_iff_exists.mp hn
  have hmove : V.map (MulAut.conj x).toMonoidHom ≠ V := fun he =>
    hxn (mem_normalizer_iff_map_conj_eq.mpr he)
  have hi := normalizer_relIndex_eq_two_of_pair H V A hpair x hx hmove
  have hd := relIndex_dvd_of_le_left H hTV
  rw [hi] at hd
  exact (T.subtype hTH).not_dvd_index hd

theorem paired_maximum_elementary_normalizer_control
    (T : Sylow 2 G) (S R V A : Subgroup G)
    (hTS : (T : Subgroup G) ≤ normalizer (S : Set G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hV : V ∈ elementaryAbelianMaxSubgroups S)
    (hRV : R ≤ normalizer (V : Set G))
    (hpair : ∀ W ∈ elementaryAbelianMaxSubgroups S,
      R ≤ normalizer (W : Set G) → W = V ∨ W = A) :
    normalizer (S : Set G) ⊓ normalizer (R : Set G) ≤ normalizer (V : Set G) := by
  apply le_normalizer_of_sylow_fixed_pair T _ V A (le_inf hTS hTR) hTV
  intro g hg
  have hS : S.map (MulAut.conj g).toMonoidHom = S := mem_normalizer_iff_map_conj_eq.mp hg.1
  have hR : R.map (MulAut.conj g).toMonoidHom = R := mem_normalizer_iff_map_conj_eq.mp hg.2
  apply hpair (V.map (MulAut.conj g).toMonoidHom)
  · have hh := (maxFamily_map_injective_iff (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective S V).mpr hV
    rwa [hS] at hh
  · have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hRV
    rwa [hR,map_equiv_normalizer_eq] at hh

variable {A : Type*} [Group A]
theorem normalizer_sylow_core_preimage_sup_kernel_eq_top
    (T : Sylow 2 G) (f : G →* A) (hf : Function.Surjective f)
    (Q : Subgroup A) [Q.Normal] (hp : IsPGroup 2 Q) :
    normalizer (((T : Subgroup G) ⊓ Q.comap f : Subgroup G) : Set G) ⊔ f.ker = ⊤ := by
  let R := (T : Subgroup G) ⊓ Q.comap f
  have hQT : Q ≤ (T.mapSurjective hf : Subgroup A) := hp.le_sylow_of_normal (T.mapSurjective hf)
  have hRm : R.map f = Q := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy.2
    · intro hx
      obtain ⟨y,hy,rfl⟩ := hQT hx
      exact ⟨y,⟨hy,hx⟩,rfl⟩
  have hRk : R ⊓ f.ker = (T : Subgroup G) ⊓ f.ker := by
    apply le_antisymm (inf_le_inf_right _ inf_le_left)
    intro x hx
    refine ⟨⟨hx.1,?_⟩,hx.2⟩
    change f x ∈ Q
    rw [MonoidHom.mem_ker.mp hx.2]
    exact Q.one_mem
  obtain ⟨P,hP⟩ := T.exists_sylow_map_eq_inf_of_normal f.ker
  have he := normalizer_map_eq_of_kernel_intersection R (T.isPGroup'.to_le inf_le_left)
    f hf P (hP.trans hRk.symm)
  rw [hRm,show normalizer (Q : Set A) = ⊤ from Q.normalizer_eq_top] at he
  have hh := congrArg (Subgroup.comap f) he
  simpa only [comap_map_eq,comap_top] using hh
end Subgroup
