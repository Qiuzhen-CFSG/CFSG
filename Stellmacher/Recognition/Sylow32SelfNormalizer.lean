module
public import Stellmacher.Recognition.Sylow32C2D8Embedding
public import Theory.SpecificGroups.CyclicTwoDihedralFourExtension
public import Theory.SpecificGroups.CyclicTwoSymmetricFourSylowNormalizer
public import Theory.SpecificGroups.AffineEight.ElementaryEight

/-!
# Self-normalization of the Sylow subgroup in the order32 C₂ × S₄ branch

A finite group with a supplied Sylow two-subgroup of order32 and an actual
maximal two-local C₂ × S₄ subgroup has a self-normalizing Sylow subgroup.
No simplicity, N₂ or additional Z condition is needed for this conclusion.

The normalized embedding supplies an elementary eight subgroup A and an
involution t with N_G(A)=C_G(t). The proved affine-eight identification
shows that the supplied Sylow acts transitively on its elementary eight
subgroups. Hence any element normalizing the Sylow differs by an element
of that Sylow from one normalizing A. This remaining element lies in C_G(t)
and normalizes the intersection of the two subgroups. The intersection is
an actual Sylow two-subgroup of C₂ × S₄ and is self-normalizing there, so
the remaining element also belongs to the supplied Sylow.

The intersection calculation and conjugation transport retain the actual
subgroup inclusions and the explicit affine coordinate map; no ambient
fusion-control assumption is used. This is the local normalizer input for
the transfer exclusion replacing the extra-Z continuation of
Kurzweil–Stellmacher, The Theory of Finite Groups, Chapter12, printed p367.
-/

namespace Stellmacher.Recognition
private abbrev DModel := Multiplicative (ZMod 2) × DihedralGroup 4
private def cPoint : DModel := (Multiplicative.ofAdd 1, 1)
private def ePoint : DModel := (1, DihedralGroup.sr 0)
private def eightPlane : Subgroup DModel := Subgroup.centralizer ({ePoint} : Set DModel)

private theorem centralizer_normalizer_intersection
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (i : DModel →* S) (hi : Function.Injective i)
    (hC : i.range = Subgroup.centralizer ({i cPoint} : Set S))
    (hModel : Nonempty (Subgroup.centralizer ({(i cPoint : G)} : Set G) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) :
    Subgroup.normalizer (S : Set G) ⊓ Subgroup.centralizer ({(i cPoint : G)} : Set G) ≤
      (S : Subgroup G) := by
  let P := Subgroup.centralizer ({(i cPoint : G)} : Set G)
  let j : DModel →* P := ((S : Subgroup G).subtype.comp i).codRestrict P (by
    intro d
    have hd : i d ∈ Subgroup.centralizer ({i cPoint} : Set S) := hC ▸ ⟨d, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hd)))
  have hj : Function.Injective j := by
    intro x y h
    apply hi
    apply Subtype.ext
    exact congrArg (fun z : P => (z : G)) h
  have hT : j.range = (S : Subgroup G).comap P.subtype := by
    ext x
    constructor
    · rintro ⟨d, rfl⟩
      exact (i d).property
    · intro hx
      let v : S := ⟨x, hx⟩
      have hv : v ∈ i.range := by
        rw [hC, Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        exact Subgroup.mem_centralizer_singleton_iff.mp x.property
      obtain ⟨d, hd⟩ := hv
      exact ⟨d, Subtype.ext (congrArg (fun z : S => (z : G)) hd)⟩
  have hTcard : Nat.card j.range = 16 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hj).toEquiv, Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card, DihedralGroup.card]
  have hPcard : Nat.card P = 48 := by
    obtain ⟨eP⟩ := hModel
    rw [Nat.card_congr eP.toEquiv, Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  let T : Sylow 2 P := Sylow.ofCard j.range (by
    rw [hTcard, hPcard]
    rw [show 48 = 2 ^ 4 * 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization])
  have hTN : Subgroup.normalizer (j.range : Set P) = j.range :=
    CyclicTwoSymmetricFour.sylow_normalizer_eq_self hModel T
  rintro g ⟨hgN, hgP⟩
  have hgp : (⟨g, hgP⟩ : P) ∈ Subgroup.normalizer (j.range : Set P) := by
    rw [hT, Subgroup.mem_normalizer_iff]
    intro x
    exact Subgroup.mem_normalizer_iff.mp hgN (x : G)
  rw [hTN, hT] at hgp
  exact hgp


private theorem conjugate_by_sylow_of_affine
    {S : Type*} [Group S] (E : Subgroup S) (e : S ≃* AffineEight.Model)
    (hE : E.map e.toMonoidHom = AffineEight.evenElementary) (α : S ≃* S) :
    ∃ s : S, E.map α.toMonoidHom = E.map (MulAut.conj s).toMonoidHom := by
  let β : AffineEight.Model ≃* AffineEight.Model := (e.symm.trans α).trans e
  let _ := AffineEight.evenElementary_isElementaryAbelian
  obtain ⟨g, hg⟩ := AffineEight.exists_conj_evenElementary
    (AffineEight.evenElementary.map β.toMonoidHom)
    (IsElementaryAbelian.map β.toMonoidHom)
    ((Subgroup.card_map_of_injective β.injective).trans AffineEight.card_evenElementary)
  refine ⟨e.symm g, ?_⟩
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  calc
    (E.map α.toMonoidHom).map e.toMonoidHom =
        (E.map e.toMonoidHom).map β.toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      apply MonoidHom.ext
      intro x
      change e (α x) = e (α (e.symm (e x)))
      rw [e.symm_apply_apply]
    _ = AffineEight.evenElementary.map β.toMonoidHom := by rw [hE]
    _ = AffineEight.evenElementary.map (MulAut.conj g).toMonoidHom := hg
    _ = (E.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom := by rw [hE]
    _ = (E.map (MulAut.conj (e.symm g)).toMonoidHom).map e.toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      apply MonoidHom.ext
      intro x
      change g * e x * g⁻¹ = e (e.symm g * x * (e.symm g)⁻¹)
      simp only [map_mul, map_inv, e.apply_symm_apply]

private theorem normalizer_eq_self_of_internal_conjugacy
    {G : Type*} [Group G] (S : Subgroup G) (E : Subgroup S)
    (hconj : ∀ α : S ≃* S,
      ∃ s : S, E.map α.toMonoidHom = E.map (MulAut.conj s).toMonoidHom)
    (hlocal : Subgroup.normalizer (S : Set G) ⊓
      Subgroup.normalizer (E.map S.subtype : Set G) ≤ S) :
    Subgroup.normalizer (S : Set G) = S := by
  apply le_antisymm _ S.le_normalizer
  intro g hg
  let α : S ≃* S := S.normalizerMonoidHom ⟨g, hg⟩
  obtain ⟨s, hs⟩ := hconj α
  let E0 := E.map S.subtype
  have hmap : E0.map (MulAut.conj g).toMonoidHom =
      E0.map (MulAut.conj (s : G)).toMonoidHom := by
    calc
      E0.map (MulAut.conj g).toMonoidHom = (E.map α.toMonoidHom).map S.subtype := by
        rw [Subgroup.map_map, Subgroup.map_map]
        rfl
      _ = (E.map (MulAut.conj s).toMonoidHom).map S.subtype := by rw [hs]
      _ = E0.map (MulAut.conj (s : G)).toMonoidHom := by
        rw [Subgroup.map_map, Subgroup.map_map]
        rfl
  have hqE : (s : G)⁻¹ * g ∈ Subgroup.normalizer (E0 : Set G) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    calc
      E0.map (MulAut.conj ((s : G)⁻¹ * g)).toMonoidHom =
          (E0.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (s : G)⁻¹).toMonoidHom := by
        conv_rhs => rw [Subgroup.map_map]
        congr 1
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      _ = (E0.map (MulAut.conj (s : G)).toMonoidHom).map
          (MulAut.conj (s : G)⁻¹).toMonoidHom := by rw [hmap]
      _ = E0 := by
        rw [Subgroup.map_map]
        have hhom : (MulAut.conj (s : G)⁻¹).toMonoidHom.comp
            (MulAut.conj (s : G)).toMonoidHom = MonoidHom.id G := by
          ext x
          simp [MulAut.conj_apply, mul_assoc]
        rw [hhom, Subgroup.map_id]
  have hqS : (s : G)⁻¹ * g ∈ Subgroup.normalizer (S : Set G) :=
    (Subgroup.normalizer (S : Set G)).mul_mem
      ((Subgroup.normalizer (S : Set G)).inv_mem (S.le_normalizer s.property)) hg
  have hq := hlocal ⟨hqS, hqE⟩
  have hmem := S.mul_mem s.property hq
  simpa only [mul_inv_cancel_left] using hmem

/-- The actual Sylow subgroup in the order32 maximal C₂ × S₄ branch is
self-normalizing. -/
public theorem sylow32_normalizer_eq_self
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hOrder : Nat.card S = 2 ^ 5) (P : Subgroup G) (hP : IsMaximalTwoLocal P)
    (hModel : Nonempty (P ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) :
    Subgroup.normalizer (S : Set G) = (S : Subgroup G) := by
  obtain ⟨i, hi, hindex, hC, hN, hNglobal, hCmodel, _⟩ :=
    sylow32_c2s4_embedding S hOrder P hP hModel
  obtain ⟨e, j, hj, he⟩ :=
    CyclicTwoDihedralFour.exists_mulEquiv_affineEight i hi hindex hC.symm hN
  let E := eightPlane.map i
  have hE : E.map e.toMonoidHom = AffineEight.evenElementary := by
    ext x
    constructor
    · rintro ⟨y, ⟨d, hd, rfl⟩, rfl⟩
      refine ⟨d, hd, ?_⟩
      change AffineEight.evenEmbedding d = e (i d)
      rw [he, hj d hd]
    · rintro ⟨d, hd, rfl⟩
      refine ⟨i d, ⟨d, hd, rfl⟩, ?_⟩
      change e (i d) = AffineEight.evenEmbedding d
      rw [he, hj d hd]
  apply normalizer_eq_self_of_internal_conjugacy (S : Subgroup G) E
    (conjugate_by_sylow_of_affine E e hE)
  change Subgroup.normalizer (S : Set G) ⊓
    Subgroup.normalizer (E.map (S : Subgroup G).subtype : Set G) ≤ _
  have hNglobal' : Subgroup.centralizer ({(i cPoint : G)} : Set G) =
      Subgroup.normalizer (E.map (S : Subgroup G).subtype : Set G) := hNglobal
  rw [← hNglobal']
  exact centralizer_normalizer_intersection S i hi hC hCmodel

end Stellmacher.Recognition
