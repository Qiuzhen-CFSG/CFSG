module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.LinearThreeSeedNormalizer
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual
public import Theory.GroupTheory.PResidual.PrimeToPerfect
public import Theory.GroupTheory.PResidual.PrimeToIntersection

/-!
# The original canonical seed excludes every normalized cubic factor

For Y = O^{3′}(NI), the actual Omega marking places Y and each original
T-conjugate in one common normal subgroup, so their mutual commutator
lies in their intersection. The actual source intersection gives Y its
placement, two-perfectness and S-normalization. Its supplied genuine S₃
quotient and the three-prime module centralizer make Y escape MI.

Starting the residual pair with the specified S-invariant cubic factor E
and reversing by the inverse conjugator now gives the canonical-seed
instance of 15.2.22: [Y,E] cannot lie in Y∩E. This is the exact consumer
needed by the binary L₃ source branch. It uses ResidualInput directly;
no partner residual identity or plane-uniqueness packet is assumed.

Source: Aschbacher--Smith, 15.2.22 and its application in 15.2.23,
printed pp.1114--1116, refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.ResidualInput
open SmallActionsSource ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

private theorem residual_normal_in_abelian_preimage
    (U : Subgroup G) (f : G →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
    (hk : f.ker ≤ U) :
    let A := (pResidual 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))).comap f
    (primeToResidual 3 U).map U.subtype ≤ A ∧
      A ≤ normalizer (((primeToResidual 3 U).map U.subtype : Subgroup G) : Set G) := by
  let R := pResidual 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
  let A := R.comap f
  let : IsMulCommutative R := IsPGroup.isMulCommutative_of_card_eq_prime_sq
    (p := 3) (show Nat.card R = 3 ^ 2 from SymmetricThreeProductResidual.residual_card)
  let g : A →* R := (f.comp A.subtype).codRestrict R (fun x => x.property)
  have hker : g.ker ≤ (A ⊓ U).subgroupOf A := by
    intro x hx
    refine ⟨x.property, hk ?_⟩
    exact congrArg Subtype.val hx
  have hnormal : ((A ⊓ U).subgroupOf A).Normal := by
    rw [← comap_map_eq_self hker]
    infer_instance
  have hn : A ≤ normalizer ((A ⊓ U : Subgroup G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mp hnormal
  have hres : primeToResidual 3 G ≤ A := by
    apply primeToResidual_le
    rw [show A = R.comap f from rfl, index_comap]
    have hi : R.index = 4 := by
      dsimp only [R]
      rw [SymmetricThreeProductResidual.residual_eq, index_prod]
      simp
    exact (show Nat.Coprime 3 R.index from hi ▸ (by decide)).coprime_dvd_right
      (R.relIndex_dvd_index_of_normal f.range)
  have he := embedded_primeToResidual_inf_eq_of_normal 3 A U hres
  refine ⟨(map_primeToResidual_le_of_hom 3 U.subtype).trans hres, ?_⟩
  rw [← he]
  exact hn.trans (normalizer_le_normalizer_characteristic_image (A ⊓ U)
    (primeToResidual 3 (A ⊓ U : Subgroup G)))

private theorem canonical_commutator
    (U : Subgroup G) (f : G →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
    (hk : f.ker ≤ U) (t : G) :
    let Y := (primeToResidual 3 U).map U.subtype
    ⁅Y, Y.map (MulAut.conj t).toMonoidHom⁆ ≤
      Y ⊓ Y.map (MulAut.conj t).toMonoidHom := by
  let A := (pResidual 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))).comap f
  let Y := (primeToResidual 3 U).map U.subtype
  obtain ⟨hYA, hAY⟩ := residual_normal_in_abelian_preimage U f hk
  have htA : t ∈ normalizer (A : Set G) := by rw [normalizer_eq_top]; trivial
  have hYtA : Y.map (MulAut.conj t).toMonoidHom ≤ A :=
    (map_mono hYA).trans_eq (mem_normalizer_iff_map_conj_eq.mp htA)
  exact le_inf
    (le_normalizer_iff_commutator_le_left.mp (hYtA.trans hAY))
    (le_normalizer_iff_commutator_le_right.mp
      (hYA.trans (normalizes_conjugate_of_normalizes htA hAY)))

private def pair_reverse {A S K : Subgroup G} {t : G}
    (p : ResidualPair A S K t) (hSA : S ≤ A) (hi : S.relIndex A = 2) :
    ResidualPair A S K t⁻¹ where
  K₁ := p.K₂
  K₂ := p.K₁
  t_mem := A.inv_mem p.t_mem
  t_not_mem := by simpa only [inv_mem_iff] using p.t_not_mem
  first := p.second
  second := p.first
  span := sup_comm _ _ |>.trans p.span
  conjugate := by
    rw [← p.conjugate, map_map]
    have he : (MulAut.conj t⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom = MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [he,map_id]
  normalized := by
    rw [←p.conjugate]
    exact normalizes_conjugate_of_normalizes
      (((normal_subgroupOf_iff_le_normalizer hSA).mp (normal_of_index_eq_two hi)) p.t_mem)
      p.normalized

variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (r : ResidualInput hsource H B)
include r

/-- Three hypotheses of 15.2.22 for the literal Y1 = O^{3′}(NI).
Its two-perfectness is a residual theorem; Y1 is not asserted to be a two-group. -/
theorem intersection_cubic_residual_basics (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I) :
    let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype
    Y ≤ M ⊓ I ∧ IsPPerfect 2 Y ∧
      planeSylow T (⁅V,B⁆ : Subgroup G) ≤ normalizer (Y : Set G) := by
  let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype
  let e : primeToResidual 3 (M ⊓ I : Subgroup G) ≃* Y :=
    (primeToResidual 3 (M ⊓ I : Subgroup G)).equivMapOfInjective
      (M ⊓ I).subtype (M ⊓ I).subtype_injective
  refine ⟨map_subtype_le _,
    (isPPerfect_primeToResidual (G := (M ⊓ I : Subgroup G)) 3 2 (by decide)).of_surjective
      e.toMonoidHom e.surjective, ?_⟩
  have hS : planeSylow T (⁅V,B⁆ : Subgroup G) ≤ M ⊓ I :=
    le_inf (inf_le_left.trans hsource.maximal.1.2)
      ((le_sup_right.trans (r.residual_sup_planeCentralizer_le hI)).trans inf_le_right)
  exact hS.trans ((M ⊓ I).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (M ⊓ I)
      (primeToResidual 3 (M ⊓ I : Subgroup G))))

/-- For the canonical seed used in the binary component, the actual Omega
image supplies the conjugate-family relation without a Frattini witness. -/
theorem canonical_seed_conjugate_commutator (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I)
    (e : (actionHom M V hsource.prepared.normalized).range ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (t : G) (ht : t ∈ (T : Subgroup G)) :
    let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype
    ⁅Y,Y.map (MulAut.conj t).toMonoidHom⁆ ≤
      Y ⊓ Y.map (MulAut.conj t).toMonoidHom := by
  let f := e.toMonoidHom.comp (actionHom M V hsource.prepared.normalized).rangeRestrict
  let U := (M ⊓ I).subgroupOf M
  have hk : f.ker ≤ U := by
    intro x hx
    have hz : (actionHom M V hsource.prepared.normalized).rangeRestrict x = 1 :=
      e.injective (hx.trans e.map_one.symm)
    have hxk : x ∈ (actionHom M V hsource.prepared.normalized).ker :=
      congrArg Subtype.val hz
    rw [actionHom_ker] at hxk
    exact ⟨x.property, r.module_centralizer_le_escape hI hxk⟩
  let a : M := ⟨t,hsource.maximal.1.2 ht⟩
  have hp := map_mono (f := M.subtype) (canonical_commutator U f hk a)
  have he : U.map M.subtype = M ⊓ I := map_subgroupOf_eq_of_le inf_le_left
  have hm : ((primeToResidual 3 U).map U.subtype).map M.subtype =
      (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype := by
    rw [map_embedded_primeToResidual_of_hom,he]
  have hc : M.subtype.comp (MulAut.conj a).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp M.subtype := by ext x; rfl
  have hcm : (((primeToResidual 3 U).map U.subtype).map
      (MulAut.conj a).toMonoidHom).map M.subtype =
      (((primeToResidual 3 U).map U.subtype).map M.subtype).map
        (MulAut.conj t).toMonoidHom := by
    rw [map_map, hc, ← map_map]
  rw [map_commutator, map_inf _ _ _ M.subtype_injective, hcm, hm] at hp
  exact hp


/-- The specialized source 15.2.22 conclusion for Y₁ = O^{3′}(NI).
The earlier Omega action and the genuine seed quotient are explicit;
both conjugate-family commutators and the normalizer contradiction are proved. -/
theorem canonical_seed_commutator_exclusion
    (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I) (hfit : generalizedFitting I = pCore 2 I)
    (e : (actionHom M V hsource.prepared.normalized).range ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (hC : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)))
    (hquot : let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype
      Nonempty (((Y ⊔ smallActionS T (⁅V,B⁆ : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Y ⊔ smallActionS T (⁅V,B⁆ : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    {t : G}
    (p : ResidualPair (T : Subgroup G) (smallActionS T (⁅V,B⁆ : Subgroup G)) (smallActionK H) t) :
    let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype
    ¬ ⁅Y,p.K₂⁆ ≤ Y ⊓ p.K₂ := by
  obtain ⟨hle,hperfect,hnormal⟩ :=
    r.intersection_cubic_residual_basics hI
  exact r.commutator_exclusion_of_residualPair hI hfit p
    ⟨hle,hperfect,hnormal,hquot⟩ hC
    (r.canonical_seed_conjugate_commutator hI e t p.t_mem)

/-- Every S-invariant normal cubic factor is excluded by the canonical seed. -/
theorem canonical_seed_exclusion_any_factor
    (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I) (hfit : generalizedFitting I = pCore 2 I)
    (e : (actionHom M V hsource.prepared.normalized).range ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (hC : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)))
    (hquot : let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype
      Nonempty (((Y ⊔ smallActionS T (⁅V,B⁆ : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Y ⊔ smallActionS T (⁅V,B⁆ : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    {E : Subgroup G} (hE : E ∈ normalCubicResiduals (smallActionK H))
    (hSE : smallActionS T (⁅V,B⁆ : Subgroup G) ≤ normalizer (E : Set G)) :
    let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype
    ¬ ⁅Y,E⁆ ≤ Y ⊓ E := by
  have hST : smallActionS T (⁅V,B⁆ : Subgroup G) < (T : Subgroup G) := lt_of_le_of_ne inf_le_left (by
    intro he
    have hi := (r.escape_index hI).2
    change (smallActionS T (⁅V,B⁆ : Subgroup G)).relIndex (T : Subgroup G) = 2 at hi
    rw [he,relIndex_self] at hi
    omega)
  obtain ⟨t,ht,htS⟩ := SetLike.exists_of_lt hST
  obtain ⟨p,hp⟩ := r.residualPair_with_first hI hE hSE t ht htS
  have hh := r.canonical_seed_commutator_exclusion hI hfit e hC hquot
    (pair_reverse p inf_le_left (r.escape_index hI).2)
  change ¬ ⁅(primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype,p.K₁⁆ ≤
    (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype ⊓ p.K₁ at hh
  rwa [hp] at hh


end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.ResidualInput
