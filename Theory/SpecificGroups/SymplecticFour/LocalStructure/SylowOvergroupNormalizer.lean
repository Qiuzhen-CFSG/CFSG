module
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.LocalCoreKernel
public import Theory.SpecificGroups.SymplecticFour.Sylow.NonsolvableOvergroups
public import Theory.SpecificGroups.SymplecticFour.Sylow.NormalizerParabolic
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SylowKernelCore

/-!
# Borel placement in symplectic normal local intersections

Let L be a normal Sp₄(2ⁿ), n > 1, in an ambient group, and let N contain
an L-Sylow subgroup and equal the normalizer of its own two-core. If
N ∩ L is proper and nonsolvable, its residual is a point or plane local
factor. An element of O₂(N) acts trivially on that factor modulo its core;
the concrete automorphism calculation makes this action inner by a member
of the local core. Thus O₂(N) splits as that core times its intersection
with C(L). The full parabolic normalizes both factors, hence lies in N.
In particular N contains the Borel over the original Sylow.

All core normality is relative to N; normality of L is relative to the
ambient group supplied here. Source: Aschbacher--Smith 15.1.19(4) and
15.1.20(3b), printed pp.1093--1097; F.1.12, printed pp.263--264.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace Theory.SpecificGroups.SymplecticFour
open DiagramAutomorphisms
variable {F A : Type*} [Field F] [Group A]

/-- Core-action detection transfers the normalizer of the local core. -/
theorem local_core_normalizer_transfer
    (L N : Subgroup A) [L.Normal] (e : Sp F ≃* L)
    (K : Subgroup (Sp F))
    (hKN : K.map (L.subtype.comp e.toMonoidHom) ≤ N)
    (hNK : N ≤ normalizer (K.map (L.subtype.comp e.toMonoidHom) : Set A))
    (hdetect : ∀ (a : MulAut (Sp F)) (hK : K.map a.toMonoidHom = K),
      (∃ k : ℕ, a^(2^k)=1) →
      (∀ x : K, restrict a K hK x / x ∈ pCore 2 K) →
      ∃ k : K, k ∈ pCore 2 K ∧ a = MulAut.conj k.val) :
    (normalizer (K.pCoreIn 2 : Set (Sp F))).map (L.subtype.comp e.toMonoidHom) ≤
      normalizer (N.pCoreIn 2 : Set A) := by
  let f := L.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp e.injective
  let R := K.map f
  have hcore : (K.pCoreIn 2).map f = R.pCoreIn 2 :=
    map_pCoreIn_of_injective 2 K f hf
  have hRQ : R.pCoreIn 2 ≤ N.pCoreIn 2 := pCoreIn_mono_of_normalizes hKN hNK
  have hmap (q : A) (hq : q ∈ N) : K.map (extensionAction L e q).toMonoidHom = K := by
    apply map_injective hf
    rw [map_map]
    have hh : f.comp (extensionAction L e q).toMonoidHom = (MulAut.conj q).toMonoidHom.comp f := by
      ext x
      exact extensionAction_apply L e q x
    rw [hh,←map_map]
    exact mem_normalizer_iff_map_conj_eq.mp (hNK hq)
  have hsplit (q : A) (hq : q ∈ N.pCoreIn 2) :
      ∃ k ∈ R.pCoreIn 2, k⁻¹*q ∈ centralizer (L : Set A) := by
    let a := extensionAction L e q
    have hqN : q ∈ N := pCoreIn_le 2 N hq
    have haK := hmap q hqN
    have ht : ∃ j : ℕ, a^(2^j)=1 := by
      obtain ⟨j,hj⟩ := (isPGroup_pCoreIn 2 N).exists_pow_pow_eq_one ⟨q,hq⟩
      refine ⟨j,?_⟩
      rw [←map_pow,show q^(2^j)=1 from congrArg Subtype.val hj,map_one]
    have hc (x : K) : restrict a K haK x / x ∈ pCore 2 K := by
      have hcomm : ⁅q,f x.val⁆ ∈ R.pCoreIn 2 := by
        apply inf_pCoreIn_le_of_le 2 hKN
        refine ⟨?_,?_⟩
        · exact R.mul_mem ((mem_normalizer_iff.mp (hNK hqN) _).mp
            (mem_map_of_mem f x.property)) (R.inv_mem (mem_map_of_mem f x.property))
        · exact (le_normalizer_iff_commutator_le_left.mp
            ((hKN.trans N.le_normalizer).trans
              (normalizer_le_normalizer_characteristic_image N (pCore 2 N))))
            (commutator_mem_commutator hq (mem_map_of_mem f x.property))
      have he : f (restrict a K haK x / x).val = ⁅q,f x.val⁆ := by
        change f (a x.val / x.val) = _
        rw [map_div]
        rw [show f (a x.val) = q*f x.val*q⁻¹ from extensionAction_apply L e q x.val]
        simp only [div_eq_mul_inv,commutatorElement_def]
      rw [←hcore,←he] at hcomm
      exact (mem_map_iff_mem K.subtype_injective).mp ((mem_map_iff_mem hf).mp hcomm)
    obtain ⟨k,hk,he⟩ := hdetect a haK ht hc
    refine ⟨f k.val,?_,?_⟩
    · rw [←hcore]
      exact mem_map_of_mem f (mem_map_of_mem K.subtype hk)
    · intro x hx
      obtain ⟨y,hy⟩ := e.surjective ⟨x,hx⟩
      have hy' : f y = x := congrArg Subtype.val hy
      have hh := extensionAction_apply L e q y
      change f (a y) = q*f y*q⁻¹ at hh
      rw [he] at hh
      change f (k.val*y*k.val⁻¹) = q*f y*q⁻¹ at hh
      simp only [map_mul,map_inv,hy'] at hh
      have hcomm : q * x * q⁻¹ = f k.val * x * (f k.val)⁻¹ := hh.symm
      calc
        x * ((f k.val)⁻¹*q) = (f k.val)⁻¹*(f k.val*x*(f k.val)⁻¹)*q := by group
        _ = (f k.val)⁻¹*(q*x*q⁻¹)*q := by rw [←hcomm]
        _ = ((f k.val)⁻¹*q)*x := by group
  apply le_normalizer_iff.mpr
  rintro x ⟨b,hb,rfl⟩ q hq
  obtain ⟨k,hk,hc⟩ := hsplit q hq
  have hbn : f b ∈ normalizer (R.pCoreIn 2 : Set A) := by
    rw [←hcore]
    exact le_normalizer_map f (mem_map_of_mem f hb)
  have hk' : f b*k*(f b)⁻¹ ∈ N.pCoreIn 2 := hRQ
    ((mem_normalizer_iff.mp hbn k).mp hk)
  have hqk : k⁻¹*q ∈ N.pCoreIn 2 := (N.pCoreIn 2).mul_mem
    ((N.pCoreIn 2).inv_mem (hRQ hk)) hq
  have hbc : (f b)*(k⁻¹*q) = (k⁻¹*q)*(f b) := hc (f b) (e b).property
  have he : f b*q*(f b)⁻¹ = (f b*k*(f b)⁻¹)*(k⁻¹*q) := by
    calc
      _ = (f b*k*(f b)⁻¹)*(f b*(k⁻¹*q)*(f b)⁻¹) := by group
      _ = _ := by rw [mul_inv_eq_iff_eq_mul.mpr hbc]
  rw [he]
  exact (N.pCoreIn 2).mul_mem hk' hqk

private theorem residual_map_of_injective {X Y : Type*} [Group X] [Group Y]
    [Finite X] (H : Subgroup X) (f : X →* Y) (hf : Function.Injective f) :
    ((solvableResidual H).map H.subtype).map f =
      (solvableResidual (H.map f)).map (H.map f).subtype := by
  let t := H.equivMapOfInjective f hf
  rw [map_map]
  have he : f.comp H.subtype = (H.map f).subtype.comp t.toMonoidHom := rfl
  rw [he,←map_map,map_solvableResidual_eq _ t.surjective]

variable [Finite F] [CharP F 2]

/-- A nonsolvable full-Sylow local intersection contains the whole Borel,
using the original ambient core-normalizer hypothesis. -/
theorem nonsolvable_local_borel_le {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1<n)
    (L N : Subgroup A) [L.Normal] (e : Sp F ≃* L)
    (S : Sylow 2 (Sp F))
    (hSN : (S : Subgroup (Sp F)).map (L.subtype.comp e.toMonoidHom) ≤ N)
    (hproper : N.comap (L.subtype.comp e.toMonoidHom) ≠ ⊤)
    (hns : ¬ Group.IsSolvable (N.comap (L.subtype.comp e.toMonoidHom)))
    (hcore : normalizer (N.pCoreIn 2 : Set A) ≤ N) :
    (normalizer (S : Set (Sp F))).map (L.subtype.comp e.toMonoidHom) ≤ N := by
  let f := L.subtype.comp e.toMonoidHom
  let H := N.comap f
  have hSH : (S : Subgroup (Sp F)) ≤ H := map_le_iff_le_comap.mp hSN
  obtain ⟨g,hg⟩ := nonsolvable_sylow_overgroup_residual hF hn S H hSH hproper hns
  let a := MulAut.conj g
  let e' : Sp F ≃* L := a.symm.trans e
  let f' := L.subtype.comp e'.toMonoidHom
  have hf' : Function.Injective f' := L.subtype_injective.comp e'.injective
  let D := H.map a.toMonoidHom
  let Q := S.mapSurjective (f := a.toMonoidHom) a.surjective
  have hQD : (Q : Subgroup (Sp F)) ≤ D := map_mono hSH
  have hDN : D.map f' = N ⊓ L := by
    ext x
    constructor
    · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
      have he : f' (a z) = f z := by simp [f',e',f]
      change f' (a z) ∈ N ⊓ L
      rw [he]
      exact ⟨hz,(e z).property⟩
    · intro hx
      obtain ⟨z,hz⟩ := e.surjective ⟨x,hx.2⟩
      have he : f z = x := congrArg Subtype.val hz
      refine ⟨a z,⟨z,?_,rfl⟩,?_⟩
      · change f z ∈ N
        rw [he]
        exact hx.1
      · simpa [f',e',f] using he
  have hND : N ≤ normalizer (D.map f' : Set A) := by
    rw [hDN]
    exact (le_inf N.le_normalizer le_normalizer_of_normal).trans
      inf_normalizer_le_normalizer_inf
  have hres (K : Subgroup (Sp F))
      (he : ((solvableResidual H).map H.subtype).map a.toMonoidHom = K) :
      (solvableResidual D).map D.subtype = K :=
    (residual_map_of_injective H a.toMonoidHom a.injective).symm.trans he
  have hKN (K : Subgroup (Sp F))
      (he : (solvableResidual D).map D.subtype = K) : K.map f' ≤ N := by
    rw [←he]
    exact (map_mono (map_subtype_le _)).trans (hDN.le.trans inf_le_left)
  have hNK (K : Subgroup (Sp F))
      (he : (solvableResidual D).map D.subtype = K) :
      N ≤ normalizer (K.map f' : Set A) := by
    rw [←he,residual_map_of_injective D f' hf']
    exact hND.trans (normalizer_le_normalizer_characteristic_image
      (D.map f') (solvableResidual (D.map f')))
  have htransport : (normalizer (S : Set (Sp F))).map f =
      (normalizer (Q : Set (Sp F))).map f' := by
    change _ = (normalizer ((S : Subgroup (Sp F)).map a.toMonoidHom : Set (Sp F))).map f'
    rw [←map_equiv_normalizer_eq,map_map]
    have he : f'.comp a.toMonoidHom = f := by
      ext z
      simp [f',e',f]
    rw [he]
    rfl
  rw [htransport]
  rcases hg with ⟨hp,hr⟩ | ⟨hp,hr⟩
  · have hr' := hres pointLocal hr
    have ht := local_core_normalizer_transfer L N e' pointLocal (hKN _ hr') (hNK _ hr')
      (point_core_inner_of_quotient_trivial hF hn)
    have hPN : pointParabolic.map f' ≤ N := by
      have hc : normalizer ((pointLocal (F := F)).pCoreIn 2 : Set (Sp F)) = pointParabolic := by
        change normalizer ((pCore 2 (pointLocal (F := F))).map pointLocal.subtype : Set (Sp F)) = _
        rw [pointLocal_core_eq hF hn]
        exact pointRadicalAmbient_normalizer hF hn
      rw [hc] at ht
      exact ht.trans hcore
    apply le_trans (map_mono ?_) hPN
    apply normalizer_le_marked_parabolic hF (by omega) Q pointParabolic (hQD.trans hp)
    exact ⟨1,Or.inl (by rw [map_one]; exact Subgroup.map_id _)⟩
  · have hr' := hres planeLocal hr
    have ht := local_core_normalizer_transfer L N e' planeLocal (hKN _ hr') (hNK _ hr')
      (plane_core_inner_of_quotient_trivial hF hn)
    have hPN : planeParabolic.map f' ≤ N := by
      have hc : normalizer ((planeLocal (F := F)).pCoreIn 2 : Set (Sp F)) = planeParabolic := by
        change normalizer ((pCore 2 (planeLocal (F := F))).map planeLocal.subtype : Set (Sp F)) = _
        rw [planeLocal_core_eq hF hn]
        exact planeRadicalAmbient_normalizer hF hn
      rw [hc] at ht
      exact ht.trans hcore
    apply le_trans (map_mono ?_) hPN
    apply normalizer_le_marked_parabolic hF (by omega) Q planeParabolic (hQD.trans hp)
    exact ⟨1,Or.inr (by rw [map_one]; exact Subgroup.map_id _)⟩
end Theory.SpecificGroups.SymplecticFour
