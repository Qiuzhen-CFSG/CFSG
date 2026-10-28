module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowOffenderPair
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowOffenderTransport
public import CFSG.Quasithin.ChapterD.Section02.Inheritance
public import Theory.Representation.BinaryOffender.CubicRatio.Equivariant

/-!
# Cubic bounds on an exchanged pair of summands

For a faithful binary action permuting two complementary subspaces of
dimension greater than two, a cubic bound of two descends to the full
stabilizer image on either summand. If a minimal cubic actor preserves the
summands, use D.2.5 on one that it moves. If it exchanges them, its stabilizer
acts faithfully on a summand and the swapped-pair codimension inequality
makes that stabilizer an FF offender. Conjugation retains the original
stabilizer action in the other orientation.

The application in `MovedCubic` uses the literal crossed moved factors of
the central Hall setup; no actor-preservation or recognition assumption is
added. Source: Aschbacher--Smith D.2.5, D.2.9 and 3.2.6(3b),
printed pp.179--182,581.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02.ChosenSource325 ChapterD
variable {A V : Type*} [Group A] [Finite A] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) A V)

private theorem conjugate_cubic (I : Submodule (ZMod 2) V) (a : A)
    (h : cubicRatio (subspaceImageRepresentation ρ (I.map (ρ a))) ≤ 2) :
    cubicRatio (subspaceImageRepresentation ρ I) ≤ 2 := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V (ρ.asGroupHom a)
  let f := MulAut.conj a
  have he (g : A) (v : V) : e (ρ g v) = ρ (f g) (e v) := by
    change ρ a (ρ g v) = ρ (a * g * a⁻¹) (ρ a v)
    simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]
  have hs (g : A) : g ∈ subspaceStabilizer ρ I ↔
      f g ∈ subspaceStabilizer ρ (I.map (ρ a)) :=
    mem_subspaceStabilizer_equivariant ρ ρ f e he I g
  let q : subspaceStabilizer ρ I →* subspaceStabilizer ρ (I.map (ρ a)) :=
    { toFun := fun g => ⟨f g,(hs g).mp g.property⟩
      map_one' := Subtype.ext f.map_one
      map_mul' := fun g k => Subtype.ext (f.map_mul g k) }
  have hq : Function.Surjective q := by
    intro g
    refine ⟨⟨f.symm g, (hs _).mpr ?_⟩,Subtype.ext (f.apply_symm_apply g)⟩
    simpa only [f.apply_symm_apply] using g.property
  let E : I ≃ₗ[ZMod 2] I.map (ρ a) := e.submoduleMap I
  have hE (g : subspaceStabilizer ρ I) (v : I.map (ρ a)) :
      stabilizerRepresentation ρ I g (E.symm v) =
        E.symm (stabilizerRepresentation ρ (I.map (ρ a)) (q g) v) := by
    apply E.injective
    rw [E.apply_symm_apply]
    apply Subtype.ext
    exact (he g (E.symm v)).trans
      (congrArg (ρ (f g)) (congrArg Subtype.val (E.apply_symm_apply v)))
  let ψ := equivariantActionImageEquiv (stabilizerRepresentation ρ I)
    (stabilizerRepresentation ρ (I.map (ρ a))) q E.symm hq hE
  let : Finite (actionImage (stabilizerRepresentation ρ I)) :=
    Finite.of_surjective _ (stabilizerRepresentation ρ I).asGroupHom.rangeRestrict_surjective
  let : Finite (actionImage (stabilizerRepresentation ρ (I.map (ρ a)))) :=
    Finite.of_surjective _ (stabilizerRepresentation ρ (I.map (ρ a))).asGroupHom.rangeRestrict_surjective
  apply cubicRatio_le_nat_of_equivariant
    (subspaceImageRepresentation ρ (I.map (ρ a)))
    (subspaceImageRepresentation ρ I) ψ.toMonoidHom ψ.injective E.symm _ 2 h
  intro d v
  change E.symm (d.val.val v) = E.symm (d.val.val (E (E.symm v)))
  rw [E.apply_symm_apply]

/-- The cubic bound passes from a faithful permuted pair to its actual
stabilizer image on either summand. -/
theorem cubicRatio_le_two_of_permuted_pair
    (hf : Function.Injective ρ) (I : Submodule (ZMod 2) V) (t : A)
    (hpair : IsCompl I (I.map (ρ t)))
    (hperm : ∀ a : A, I.map (ρ a) = I ∨ I.map (ρ a) = I.map (ρ t))
    (hdim : 2 < Module.finrank (ZMod 2) I)
    (hbound : cubicRatio ρ ≤ 2) :
    cubicRatio (subspaceImageRepresentation ρ I) ≤ 2 := by
  obtain ⟨E,hE⟩ := (QhatStar_nonempty_iff ρ).mpr hbound
  have hel := hE.1.2.1
  have hc := hE.1.2.2.1
  let : IsElementaryAbelian 2 E := hel.2
  have hd : fixedCodim ρ E ≤ 2 * rank E := by
    have hh := hE.1.2.2.2.le.trans hbound
    exact (actionRatio_le_nat_iff ρ hel 2).mp hh
  have hI : I ≠ ⊥ := by
    intro he
    rw [he,finrank_bot] at hdim
    omega
  by_cases hstable : E ≤ subspaceStabilizer ρ I
  · have hrestrict (J : Submodule (ZMod 2) V)
        (hJ : E ≤ subspaceStabilizer ρ J) (hn : ¬ J ≤ fixedSpace ρ E) :
        cubicRatio (subspaceImageRepresentation ρ J) ≤ 2 := by
      have hr := RPlusBound.restricted ρ
        (show E ∈ RPlusBound ρ 2 from ⟨⟨hel,hE.1.2.2.2.le.trans hbound⟩,
          QhatStar.mem_RPlus ρ hE⟩) J hJ hn
      have hcu := isCubic_restrictedSubgroup ρ J hc
      have hlow : cubicRatio (subspaceImageRepresentation ρ J) ≤
          actionRatio (subspaceImageRepresentation ρ J) (restrictedSubgroup ρ J E) :=
        iInf_le_of_le _ (iInf_le_of_le ⟨hr.1,hcu⟩ le_rfl)
      exact hlow.trans hr.2
    by_cases hn : I ≤ fixedSpace ρ E
    · have hJ : E ≤ subspaceStabilizer ρ (I.map (ρ t)) := by
        intro e he
        apply (subspace_map_eq_iff ρ _ e).mp
        have hfix := (subspace_map_eq_iff ρ I e).mpr (hstable he)
        rcases hperm (e*t) with hh | hh
        · have hbad : I.map (ρ t) = I := by
            have h := congrArg (fun J : Submodule (ZMod 2) V => J.map (ρ e⁻¹)) hh
            rw [←subspace_map_mul,inv_mul_cancel_left] at h
            rw [(subspace_map_eq_iff ρ I e⁻¹).mpr
              ((subspaceStabilizer ρ I).inv_mem (hstable he))] at h
            exact h
          exact (hI (hpair.disjoint.eq_bot_of_le hbad.ge)).elim
        · simpa only [subspace_map_mul] using hh
      apply conjugate_cubic ρ I t (hrestrict _ hJ ?_)
      intro hnf
      obtain ⟨a,ha,ha1⟩ := (Subgroup.bot_or_exists_ne_one E).resolve_left hel.1
      apply ha1
      apply hf
      apply LinearMap.ext
      intro v
      obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp
        (hpair.sup_eq_top ▸ (show v ∈ (⊤ : Submodule (ZMod 2) V) from trivial))
      rw [map_add,map_one,Module.End.one_apply]
      exact congrArg₂ (· + ·) (hn hx ⟨a,ha⟩) (hnf hy ⟨a,ha⟩)
    · exact hrestrict I hstable hn
  · obtain ⟨a,ha,has⟩ := Set.not_subset.mp hstable
    have hm : I.map (ρ a) ≠ I := fun he => has ((subspace_map_eq_iff ρ I a).mp he)
    have hat : I.map (ρ a) = I.map (ρ t) := (hperm a).resolve_left hm
    have ha2 : a*a = 1 := by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
    have htwo : ∀ b ∈ E, I.map (ρ b) = I ∨ I.map (ρ b) = I.map (ρ a) := by
      intro b _
      rw [hat]
      exact hperm b
    have hdis : Disjoint I (I.map (ρ a)) := hat ▸ hpair.disjoint
    let B := E ⊓ subspaceStabilizer ρ I
    have hB : B ≠ ⊥ := by
      intro hb
      have hr := pair_stabilizer_rank ρ I E hel ha ha2 hm htwo
      change rank E = rank B + 1 at hr
      rw [hb,BinaryOffender.rank_bot,zero_add] at hr
      have hl := swapped_pair_codim_lower_bound ρ I E ha ha2 hdis
      rw [hr] at hd
      omega
    have hk : subspaceKernel ρ I B = ⊥ := by
      apply bot_unique
      rintro b ⟨hb,hbI⟩
      apply hf
      apply LinearMap.ext
      intro v
      obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp
        (hpair.sup_eq_top ▸ (show v ∈ (⊤ : Submodule (ZMod 2) V) from trivial))
      rw [←hat] at hy
      obtain ⟨z,hz,rfl⟩ := hy
      have hba : b*a = a*b := congrArg Subtype.val
        (mul_comm (⟨b,hb.1⟩ : E) ⟨a,ha⟩)
      rw [map_add,map_one,Module.End.one_apply,hbI x hx]
      congr 1
      calc
        ρ b (ρ a z) = ρ (b*a) z := (congrFun (congrArg DFunLike.coe (ρ.map_mul b a)) z).symm
        _ = ρ (a*b) z := by rw [hba]
        _ = ρ a (ρ b z) := congrFun (congrArg DFunLike.coe (ρ.map_mul a b)) z
        _ = ρ a z := by rw [hbI z hz]
    have hoff := pair_stabilizer_isOffender ρ I hI E hel ha ha2 hdis hm htwo hB hk hd
    exact (cubicRatio_le_quadraticRatio _).trans
      (((isFFModule_iff_quadraticRatio_le_one _).mp ⟨_,hoff⟩).trans (by norm_num))
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
