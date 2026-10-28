module
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.GroupTheory.PResidual.SylowSupplement
/-!
# Residual conjugators generating binary SL2 with two Sylows

A proper overgroup of a defining-characteristic Sylow subgroup of SL2 lies
in its normalizer, by the actual upper/lower root calculation transported
through Sylow conjugacy. A conjugate contained in that normalizer must be
the same Sylow. Consequently a conjugator outside the normalizer gives two
Sylows generating the full matrix group.

For any finite group mapping onto SL2, its two-residual supplements its
Sylow subgroup. The residual therefore contains an element whose image is
outside the proper Sylow normalizer. The conclusion retains that original
element and both literal subgroup images under the supplied quotient map.
This works also over F2; no perfectness or solvability branch is required.
Source: Aschbacher--Smith B.6.10, printed p.117, hypothesis B.2.18(d).
-/
public noncomputable section
open Subgroup
open scoped MatrixGroups
private theorem sylow_join_conjugate {D : Type*} [Group D] {p : ℕ} (S : Sylow p D)
    (hproper : ∀ K : Subgroup D, (S : Subgroup D) ≤ K → K ≠ ⊤ → K ≤ normalizer (S : Set D))
    {g : D} (hg : g ∉ normalizer (S : Set D)) :
    (S : Subgroup D) ⊔ (S : Subgroup D).map (MulAut.conj g).toMonoidHom = ⊤ := by
  by_contra hn
  let Q : Sylow p D := g • S
  have hQ : (Q : Subgroup D) = (S : Subgroup D).map (MulAut.conj g).toMonoidHom := rfl
  have hle := hproper _ le_sup_left hn
  have hQN : (Q : Subgroup D) ≤ normalizer (S : Set D) := by
    rw [hQ]
    exact le_sup_right.trans hle
  have hQS : (Q : Subgroup D) ≤ (S : Subgroup D) := by
    have hh := Q.isPGroup'.inf_normalizer_sylow S
    rw [inf_eq_left.mpr hQN] at hh
    exact inf_eq_left.mp hh.symm
  have he : Q = S := Sylow.ext (Q.is_maximal' S.isPGroup' hQS).symm
  exact hg (Sylow.smul_eq_iff_mem_normalizer.mp he)


namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Every proper overgroup of a Sylow two-subgroup lies in its actual normalizer. -/
theorem overgroup_le_sylowNormalizer (S : Sylow 2 (SL(2,F)))
    {K : Subgroup (SL(2,F))} (hSK : (S : Subgroup _) ≤ K) (hK : K ≠ ⊤) :
    K ≤ normalizer (S : Set (SL(2,F))) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (SL(2,F)) (upperUnipotentSylow F 2) S
  let e := (MulAut.conj g).toMonoidHom
  have hS : (upperUnipotent F).map e = (S : Subgroup (SL(2,F))) := by
    exact congrArg (fun P : Sylow 2 (SL(2,F)) => P.toSubgroup) hg
  have hUK : upperUnipotent F ≤ K.comap e := map_le_iff_le_comap.mp (hS ▸ hSK)
  have hK' : K.comap e ≠ ⊤ := by
    intro he
    apply hK
    rw [← map_comap_eq_self_of_surjective (f := e) (MulAut.conj g).surjective K,he,
      map_top_of_surjective _ (MulAut.conj g).surjective]
  have hh := map_mono (f := e) (overgroup_le_rankOneBorel hUK hK')
  rw [map_comap_eq_self_of_surjective (f := e) (MulAut.conj g).surjective K] at hh
  change K ≤ (normalizer (upperUnipotent F : Set (SL(2,F)))).map e at hh
  rw [map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective,hS] at hh
  exact hh

/-- A Sylow two-subgroup and any conjugate by an element outside its normalizer generate SL2. -/
theorem sylow_sup_conjugate_eq_top_of_not_mem_normalizer
    (S : Sylow 2 (SL(2,F))) {g : SL(2,F)}
    (hg : g ∉ normalizer (S : Set (SL(2,F)))) :
    (S : Subgroup (SL(2,F))) ⊔ (S : Subgroup (SL(2,F))).map (MulAut.conj g).toMonoidHom = ⊤ :=
  sylow_join_conjugate S (fun _ hSK hK => overgroup_le_sylowNormalizer S hSK hK) hg

variable {H : Type*} [Group H] [Finite H]
/-- The original two-residual contains a conjugator whose two literal Sylow images generate SL2. -/
theorem exists_residual_conjugate_sylow_image_sup_eq_top
    (T : Sylow 2 H) (q : H →* SL(2,F)) (hq : Function.Surjective q) :
    ∃ g : H, g ∈ pResidual 2 H ∧
      (T : Subgroup H).map q ⊔
        (((T : Subgroup H).map (MulAut.conj g).toMonoidHom).map q) = ⊤ := by
  let S := T.mapSurjective hq
  have hR : ¬ (pResidual 2 H).map q ≤ normalizer (S : Set (SL(2,F))) := by
    intro hr
    have hh := congrArg (fun A : Subgroup H => A.map q) (pResidual_sup_sylow_eq_top T)
    rw [Subgroup.map_sup,map_top_of_surjective _ hq] at hh
    have htop : (⊤ : Subgroup (SL(2,F))) ≤ normalizer (S : Set (SL(2,F))) := by
      rw [← hh]
      apply sup_le hr
      change (S : Subgroup (SL(2,F))) ≤ normalizer (S : Set (SL(2,F)))
      exact (S : Subgroup (SL(2,F))).le_normalizer
    exact no_normal_sylow F 2 S (normalizer_eq_top_iff.mp (top_unique htop))
  obtain ⟨x,hx,hxn⟩ := SetLike.not_le_iff_exists.mp hR
  obtain ⟨g,hg,rfl⟩ := mem_map.mp hx
  refine ⟨g,hg,?_⟩
  have hgen := sylow_sup_conjugate_eq_top_of_not_mem_normalizer S hxn
  have he : ((T : Subgroup H).map (MulAut.conj g).toMonoidHom).map q =
      ((T : Subgroup H).map q).map (MulAut.conj (q g)).toMonoidHom := by
    rw [Subgroup.map_map,Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change q (g * x * g⁻¹) = q g * q x * (q g)⁻¹
    simp only [map_mul,map_inv]
  rw [he]
  exact hgen
end Matrix.SpecialLinearGroup
