module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.Generation
public import Theory.Representation.BinaryPermutation.SixOrbitPreservation
public import Theory.GroupTheory.ConjugationOrbitSize

/-!
# Normalizers of the nonsingular moved module

The six-letter addition-graph calculation separates the two equal-sized
nonconstant orbits. Transport through the genuine core marking therefore
shows that an element normalizing both L_v and V_v preserves every actual
L_v-orbit on V_v. On a weight-two vector it differs from an L_v-element by
a point centralizer. If these point centralizers normalize the corresponding
residuals, all the generating residuals remain in L, so the actor normalizes L.

PreferredPoint supplies the point-normalizer premise from the source choice
of v. This yields the nonnormality reduction in Aschbacher--Smith, combined
manuscript (1 March 2004), Lemma 12.6.11, printed p.825, preserving the
original V_v, conjugation, and quotient marking.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation BinaryPermutation.EightNonsingular
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

omit [Finite G] in
private theorem conjugacyOrbit_image (A : Subgroup G) (x t : G)
    (ht : t ∈ normalizer (A : Set G)) :
    (MulAut.conj t) '' conjugacyOrbit A x = conjugacyOrbit A (t*x*t⁻¹) := by
  ext y
  constructor
  · rintro ⟨_,⟨a,rfl⟩,rfl⟩
    refine ⟨⟨t*a*t⁻¹,(ht a).mp a.property⟩,?_⟩
    simp [MulAut.conj_apply,mul_assoc]
  · rintro ⟨a,rfl⟩
    have ha : t⁻¹ * (a : G) * t ∈ A := by
      simpa using ((normalizer (A : Set G)).inv_mem ht a).mp a.property
    refine ⟨(t⁻¹*a*t)*x*(t⁻¹*a*t)⁻¹,⟨⟨_,ha⟩,rfl⟩,?_⟩
    simp [MulAut.conj_apply,mul_assoc]

omit [Finite G] in
private theorem orbit_control_of_marking
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {A : Type*} [Group A] (ρ : Representation (ZMod 2) A W)
    (E : Additive V ≃ₗ[ZMod 2] W)
    (f : L →* A) (hf : Function.Surjective f)
    (hn : L ≤ normalizer (V : Set G))
    (hE : ∀ l w, E (seedRepresentation L V hn l w) = ρ (f l) (E w))
    (horbit : ∀ e : W ≃+ W,
      (∀ x, e '' (Set.range fun a : A => ρ a x) =
        Set.range fun a : A => ρ a (e x)) →
      ∀ x, ∃ a : A, ρ a x = e x)
    (n : G) (hnL : n ∈ normalizer (L : Set G))
    (hnV : n ∈ normalizer (V : Set G)) (v : V) :
    ∃ l : L, n * (v : G) * n⁻¹ = (l : G) * v * (l : G)⁻¹ := by
  let j : W → G := fun w => ((E.symm w).toMul : G)
  have hseed (l : L) (w : Additive V) :
      ((seedRepresentation L V hn l w).toMul : G) =
        (l : G) * (w.toMul : G) * (l : G)⁻¹ := rfl
  have hj : Function.Injective j :=
    Subtype.val_injective.comp (Additive.toMul.injective.comp E.symm.injective)
  have hmodel (x : W) :
      j '' (Set.range fun a : A => ρ a x) = conjugacyOrbit L (j x) := by
    ext y
    constructor
    · rintro ⟨_,⟨a,rfl⟩,rfl⟩
      obtain ⟨l,rfl⟩ := hf a
      refine ⟨l,?_⟩
      have he := hE l (E.symm x)
      rw [E.apply_symm_apply] at he
      have hh := congrArg j he
      simpa only [j,E.symm_apply_apply,hseed] using hh
    · rintro ⟨l,rfl⟩
      refine ⟨_,⟨f l,rfl⟩,?_⟩
      have he := hE l (E.symm x)
      rw [E.apply_symm_apply] at he
      have hh := congrArg j he
      exact (show (l : G) * j x * (l : G)⁻¹ = j (ρ (f l) x) from by
        simpa only [j,E.symm_apply_apply,hseed] using hh).symm
  let c := V.normalizerMonoidHom ⟨n,hnV⟩
  let e : W ≃+ W := E.symm.toAddEquiv.trans (c.toAdditive.trans E.toAddEquiv)
  have he (x : W) : j (e x) = n * j x * n⁻¹ := by
    change ((E.symm (E (c.toAdditive (E.symm x)))).toMul : G) = _
    rw [E.symm_apply_apply]
    rfl
  have ho (x : W) :
      e '' (Set.range fun a : A => ρ a x) = Set.range fun a : A => ρ a (e x) := by
    apply Set.image_injective.mpr hj
    rw [Set.image_image]
    have he' : (fun x => j (e x)) = (fun x => MulAut.conj n (j x)) := funext he
    rw [he', ← Set.image_image]
    change (MulAut.conj n) '' (j '' _) = j '' _
    rw [hmodel,hmodel,conjugacyOrbit_image L _ n hnL]
    exact congrArg (conjugacyOrbit L) (he x).symm
  obtain ⟨a,ha⟩ := horbit e ho (E (Additive.ofMul v))
  have hm : j (e (E (Additive.ofMul v))) ∈
      conjugacyOrbit L (j (E (Additive.ofMul v))) := by
    rw [← hmodel]
    exact ⟨_,⟨a,ha⟩,rfl⟩
  obtain ⟨l,hl⟩ := hm
  refine ⟨l,?_⟩
  rw [he] at hl
  simpa only [j,E.symm_apply_apply, toMul_ofMul] using hl.symm


/-- Normalizing the marked local core and its actor preserves every actual orbit. -/
theorem OrthogonalMarking.local_moved_orbit_control
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (g : G) (hgA : g ∈ normalizer (Lv L (v : G) : Set G))
    (hgW : g ∈ normalizer (Vv L V (v : G) : Set G))
    (u : Vv L V (v : G)) :
    ∃ l : Lv L (v : G), g * (u : G) * g⁻¹ = (l : G) * u * (l : G)⁻¹ := by
  let := Vv_elementary chosen.normalizes (v : G)
  obtain ⟨i,j,hij,hp⟩ := nonsingular_pair _ hv
  obtain ⟨E,hE,_⟩ := D.local_core_marking chosen v i j hij hp
  apply orbit_control_of_marking (alternatingCoreRepresentation (Fin 6)) E.symm
    (D.localSixMap v i j hij hp) (D.localSixMap_surjective v i j hij hp)
    (Lv_normalizes_Vv L V (v : G)) ?_ six_core_orbit_preserved g hgA hgW u
  intro l w
  apply E.injective
  rw [E.apply_symm_apply,hE,E.apply_symm_apply]

/-- The point-normalizer bound and the literal generation theorem control
any actor normalizing both L_v and V_v. -/
theorem SourceHypothesis.local_moved_normalizer_control
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v) :
    let := Vv_elementary H.chosen.normalizes (v : G)
    ∀ (E : core (Fin 6) ≃ₗ[ZMod 2] Additive (Vv L V (v : G))),
      weightTwoResiduals L (Vv L V (v : G)) E = L →
      (∀ u ∈ weightTwoPoints (Vv L V (v : G)) E,
        Gv u ≤ normalizer (Lv L u : Set G)) →
      normalizer (Lv L (v : G) : Set G) ⊓ normalizer (Vv L V (v : G) : Set G) ≤ M L := by
  let := Vv_elementary H.chosen.normalizes (v : G)
  dsimp only
  intro E hgen hpoints g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · conv_lhs => rw [←hgen,weightTwoResiduals,Subgroup.map_iSup]
    apply iSup_le
    intro u
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro hu
    have huW : u ∈ Vv L V (v : G) := by
      obtain ⟨w,_,rfl⟩ := hu
      exact (E w).toMul.property
    obtain ⟨l,hl⟩ := D.local_moved_orbit_control H.chosen v hv g hg.1 hg.2 ⟨u,huW⟩
    have hq : (l : G)⁻¹ * g ∈ Gv u := by
      rw [Gv,mem_centralizer_singleton_iff]
      have hh : ((l : G)⁻¹*g)*u*((l : G)⁻¹*g)⁻¹ = u := by
        calc
          _ = (l : G)⁻¹*(g*u*g⁻¹)*(l : G) := by group
          _ = _ := by rw [hl]; group
      exact mul_inv_eq_iff_eq_mul.mp hh
    have hqN := hpoints u hu hq
    rintro _ ⟨x,hx,rfl⟩
    have hxL := Lv_le_L L u ((hqN x).mp hx)
    have hlL := Lv_le_L L (v : G) l.property
    have ht := (L.le_normalizer hlL ((l : G)⁻¹*g*x*((l : G)⁻¹*g)⁻¹)).mp hxL
    convert ht using 1
    simp [MulAut.conj_apply,mul_assoc]
  · rw [card_map_of_injective (MulAut.conj g).injective]

end CFSG.Quasithin.Chapter12.Section06
