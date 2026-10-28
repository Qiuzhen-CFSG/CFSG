module
public import Theory.SpecificGroups.ReeF4.SourceCompletion.CartanReflections
public import Theory.SpecificGroups.ReeF4.OddSupplement
public import Theory.GroupTheory.Hall.Conjugacy
public import Theory.GroupTheory.Hall.OddNormalProducts
public import Theory.GroupTheory.Amalgam.RankTwo


/-!
# Compatible local Ree actions preserve the mixed Weyl relation

Hall conjugacy in the full solvable Borel provides one common inner
adjustment of its Cartan. The two compatible parabolic actions then send
the marked reflections to Cartan-normalizing elements outside the Borel.
The native Cartan/reflection calculation gives the eighth-power relation;
removing the common conjugation gives it in the original marking.

The inputs are local automorphisms and their actual inclusion equations.
No action on the complete native model is assumed. This is the relation
preservation step in constructing the source 5.3.2 extension; the compatible
global extension and full-normalizer diagram are further steps.
Source: Aschbacher–Smith 5.3.2 and F.4.3,10,16, printed pp.659,274,279,282;
GLS3 2.3.4 and Table 2.4 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public noncomputable section
namespace ReeF4.SourceCompletion
open Subgroup Parabolics LargeLocalSeeds Theory.GroupTheory

private theorem hall_adjustment {F : Type*} [Group F] [Finite F]
    (hsol : Group.IsSolvable F) (π : Set Nat.Primes) (K : Subgroup F)
    (hK : IsHallSubgroup π K) (a : MulAut F) :
    ∃ b : F, K.map (MulAut.conj b * a).toMonoidHom=K := by
  obtain ⟨b,hb⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable hsol (hK.map_mulAut a) hK
  refine ⟨b,?_⟩
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    exact hb.ge ⟨a y,⟨y,hy,rfl⟩,rfl⟩
  · intro x hx
    obtain ⟨y,⟨z,hz,rfl⟩,hy⟩ := hb.le hx
    exact ⟨z,hz,hy⟩

abbrev nativeAmalgam (m : ℕ) : RankTwoAmalgam
    (parabolic m .linear) (borel m) (parabolic m .suzuki) := RankTwoAmalgam.ofSubgroups
  (parabolic m .linear) (borel m) (parabolic m .suzuki)
  (borel_le_parabolic m .linear) (borel_le_parabolic m .suzuki)

/-- Every automorphism of the entire native Borel has a genuine inner
adjustment preserving its fixed Cartan subgroup. -/
theorem borel_action_cartan_adjustment (m : ℕ) (a : MulAut (borel m)) :
    ∃ b : borel m,
      ((fixedTorus m).subgroupOf (borel m)).map
        ((MulAut.conj b * a).toMonoidHom) = (fixedTorus m).subgroupOf (borel m) := by
  let K := (fixedTorus m).subgroupOf (borel m)
  have hK : IsHallSubgroup OddHall.oddPrimes K :=
    OddHall.oddHall_of_normalized_sup (unipotent_isPGroup m)
      (Parabolics.fixedTorus_odd_card m (SectionGeometry.BNPair.splitTorus_card_odd m)).coprime_two_left
      ((fixedTorus_le_borel m).trans (borel_le_unipotent_normalizer m))
      (borel_eq_unipotent_sup_fixedTorus m).symm
  exact hall_adjustment (OddSupplement.borel_isSolvable m) OddHall.oddPrimes K hK a

private theorem adjusted_endpoint_cartan {F : Type*} [Group F] (K B P : Subgroup F) (hKB : K ≤ B) (hBP : B ≤ P)
    (a : MulAut P) (c : MulAut B)
    (ha : ∀ z : B, (a (inclusion (hBP) z)).val=(c z).val)
    (b : B)
    (hb : (K.subgroupOf B).map
      (MulAut.conj b * c).toMonoidHom = K.subgroupOf B) :
    (K.subgroupOf P).map
      (P.subtype.comp
        (MulAut.conj (inclusion (hBP) b) * a).toMonoidHom) = K := by
  let f := P.subtype.comp
    (MulAut.conj (inclusion (hBP) b) * a).toMonoidHom
  have h := congrArg (fun K : Subgroup B => K.map B.subtype) hb
  rw [Subgroup.map_map,subgroupOf_map_subtype,inf_eq_left.mpr (hKB)] at h
  conv_rhs => rw [←h]
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    refine ⟨⟨z.val,hKB hz⟩,hz,?_⟩
    change b.val*(c ⟨z.val,_⟩).val*b.val⁻¹=b.val*(a z).val*b.val⁻¹
    rw [←ha]
    rfl
  · rintro ⟨z,hz,rfl⟩
    refine ⟨inclusion (hBP) z,hz,?_⟩
    change b.val*(a (inclusion (hBP) z)).val*b.val⁻¹=
      b.val*(c z).val*b.val⁻¹
    rw [ha]

private theorem adjusted_normalizes {F : Type*} [Group F] (K B P : Subgroup F) (hKB : K ≤ B) (hBP : B ≤ P)
    (a : MulAut P) (c : MulAut B)
    (ha : ∀ z : B, (a (inclusion (hBP) z)).val=(c z).val)
    (b : B)
    (hb : (K.subgroupOf B).map
      (MulAut.conj b * c).toMonoidHom = K.subgroupOf B) :
    ∀ x : P, x.val ∈ normalizer (K : Set F) →
    b.val*(a x).val*b.val⁻¹ ∈
      normalizer (K : Set F) := by
  intro x hx
  let f := P.subtype.comp
    (MulAut.conj (inclusion (hBP) b) * a).toMonoidHom
  have hn : x ∈
      normalizer (K.subgroupOf P : Set P) := by
    rw [←subgroupOf_normalizer_eq ((hKB).trans (hBP))]
    exact hx
  have hh := (le_normalizer_map f) ⟨x,hn,rfl⟩
  rw [adjusted_endpoint_cartan K B P hKB hBP a c ha b hb] at hh
  exact hh

private theorem endpoint_out {F : Type*} [Group F] (B P : Subgroup F) (hBP : B ≤ P)
    (a : MulAut P) (c : MulAut B)
    (ha : ∀ z : B, (a (inclusion (hBP) z)).val=(c z).val) :
    ∀ x : P, x.val ∉ B → (a x).val ∉ B := by
  intro x hxb hx
  let z : B := ⟨(a (x)).val,hx⟩
  have he : a (inclusion (hBP) (c.symm z)) = a (x) := by
    apply Subtype.ext
    rw [ha,c.apply_symm_apply]
  have hh := congrArg Subtype.val (a.injective he)
  exact hxb (hh ▸ (c.symm z).property)

/-- Every compatible native parabolic automorphism preserves the literal
mixed eighth-power relation. No global automorphism is supplied as input. -/
theorem compatible_reflection_product_eight {m : ℕ} (hm : 0<m)
    (l : MulAut (parabolic m .linear)) (r : MulAut (parabolic m .suzuki))
    (c : MulAut (borel m))
    (hl : ∀ z : borel m, (l (inclusion (borel_le_parabolic m .linear) z)).val=(c z).val)
    (hr : ∀ z : borel m, (r (inclusion (borel_le_parabolic m .suzuki) z)).val=(c z).val) :
    ((l (SmallCompletion.reflection m .linear)).val *
      (r (SmallCompletion.reflection m .suzuki)).val)^8=1 := by
  obtain ⟨b,hb⟩ := borel_action_cartan_adjustment m c
  let x := (l (SmallCompletion.reflection m .linear)).val
  let y := (r (SmallCompletion.reflection m .suzuki)).val
  have hx := adjusted_normalizes (fixedTorus m) (borel m) (parabolic m .linear)
    (fixedTorus_le_borel m) (borel_le_parabolic m .linear) l c hl b hb
      (SmallCompletion.reflection m .linear) (SmallCompletion.reflection_mem_normalizer_fixedTorus m .linear)
  have hy := adjusted_normalizes (fixedTorus m) (borel m) (parabolic m .suzuki)
    (fixedTorus_le_borel m) (borel_le_parabolic m .suzuki) r c hr b hb
      (SmallCompletion.reflection m .suzuki) (SmallCompletion.reflection_mem_normalizer_fixedTorus m .suzuki)
  have hxb : b.val*x*b.val⁻¹∉borel m := by
    intro hx
    exact endpoint_out (borel m) (parabolic m .linear) (borel_le_parabolic m .linear) l c hl
        (SmallCompletion.reflection m .linear) (SmallCompletion.reflection_not_mem_borel m .linear)
      ((mem_normalizer_iff.mp ((borel m).le_normalizer b.property) x).mpr hx)
  have hyb : b.val*y*b.val⁻¹∉borel m := by
    intro hy
    exact endpoint_out (borel m) (parabolic m .suzuki) (borel_le_parabolic m .suzuki) r c hr
        (SmallCompletion.reflection m .suzuki) (SmallCompletion.reflection_not_mem_borel m .suzuki)
      ((mem_normalizer_iff.mp ((borel m).le_normalizer b.property) y).mpr hy)
  have h := torus_reflection_product_eight (m := m) hm (b.val*x*b.val⁻¹) (b.val*y*b.val⁻¹)
    ((parabolic m .linear).mul_mem ((parabolic m .linear).mul_mem
      (borel_le_parabolic m .linear b.property) (l _).property)
        (inv_mem (borel_le_parabolic m .linear b.property)))
    ((parabolic m .suzuki).mul_mem ((parabolic m .suzuki).mul_mem
      (borel_le_parabolic m .suzuki b.property) (r _).property)
        (inv_mem (borel_le_parabolic m .suzuki b.property))) hx hy hxb hyb
  have he : (MulAut.conj b.val) ((x*y)^8)=1 := by
    simpa only [map_pow,map_mul,MulAut.conj_apply] using h
  exact (MulAut.conj b.val).map_eq_one_iff.mp he
private theorem left_compat {F : Type*} [Group F]
    (P B Q : Subgroup F) (hP : B ≤ P) (hQ : B ≤ Q)
    (a : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P B Q hP hQ)
      (RankTwoAmalgam.ofSubgroups P B Q hP hQ)) (z : B) :
    (a.left (inclusion hP z)).val=(a.middle z).val :=
  congrArg (fun x : P => x.val) (a.left_commutes z)
private theorem right_compat {F : Type*} [Group F]
    (P B Q : Subgroup F) (hP : B ≤ P) (hQ : B ≤ Q)
    (a : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P B Q hP hQ)
      (RankTwoAmalgam.ofSubgroups P B Q hP hQ)) (z : B) :
    (a.right (inclusion hQ z)).val=(a.middle z).val :=
  congrArg (fun x : Q => x.val) (a.right_commutes z)
/-- The compatible amalgam action preserves the marked native relation. -/
theorem iso_reflection_product_eight {m : ℕ} (hm : 0<m)
    (a : RankTwoAmalgam.Iso (nativeAmalgam m) (nativeAmalgam m)) :
    ((a.left (SmallCompletion.reflection m .linear)).val *
      (a.right (SmallCompletion.reflection m .suzuki)).val)^8=1 := by
  have hl := left_compat (parabolic m .linear) (borel m) (parabolic m .suzuki)
    (borel_le_parabolic m .linear) (borel_le_parabolic m .suzuki) a
  have hr := right_compat (parabolic m .linear) (borel m) (parabolic m .suzuki)
    (borel_le_parabolic m .linear) (borel_le_parabolic m .suzuki) a
  exact compatible_reflection_product_eight (m := m) hm a.left a.right a.middle hl hr
end ReeF4.SourceCompletion
