module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationAction
public import Theory.Alternating.OddCentralCovers
public import Theory.Alternating.HexEvenQuasisimpleExtension
public import Theory.GroupTheory.PCoreInRestriction

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationPoint

/-!
# The covered augmentation action and the literal point residual

The original five-dimensional core marking supplies the central quotient
of L/O₂(L), with its actual conjugation action. The two-core of C_LT(z)
fixes the cubic center: its commutators with O₂,Z(L) lie in O₂(L).
A transposition would induce an outer involution of the perfect triple
cover and invert that center. Thus the covered point radical has no
transposition in the original augmentation action.

The same original marking makes C_L(z) a {2,3}-group in the covered row.
Consequently its two-residual equals its prime-to-three residual, and
adjoining T identifies the literal L₁T with C_LT(z). Both nonconstant
weight orbits are retained. No four-dimensional NaturalSetup is used.
AugmentationCoveredComparison applies these results to the actual Thompson
and Baumann subgroups in the nonsolvable-centralizer argument.

Source: Aschbacher–Smith 13.2.2(8), printed pp.877–878, and 13.4.10,
printed p.908; GLS3 5.2.7 supplies the proved triple-cover center inversion.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (D : ChosenModule T L V) (m : CoreMarking D)
noncomputable def augmentationCentralQuotient :
    ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃* alternatingGroup (Fin 6) := by
  let q := QuotientGroup.mk' (pCore 2 L)
  let f := (QuotientGroup.mk' (center (L ⧸ pCore 2 L))).comp q
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp
    (QuotientGroup.mk'_surjective _)
  have hk : f.ker = centralCore L := by
    change ((QuotientGroup.mk' (center (L ⧸ pCore 2 L))).comp q).ker = _
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  let e : (L ⧸ centralCore L) ≃* ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  exact e.symm.trans m.quotient

omit [Finite G] in
theorem augmentationCentralQuotient_apply (l : L) :
    augmentationCentralQuotient D m
      (QuotientGroup.mk' (center (L ⧸ pCore 2 L)) (QuotientGroup.mk' (pCore 2 L) l)) =
        m.quotient (QuotientGroup.mk' (centralCore L) l) := by
  unfold augmentationCentralQuotient
  change m.quotient _ = m.quotient _
  congr 1
  apply (Equiv.symm_apply_eq _).mpr
  rfl

noncomputable def augmentationQuotientAction :
    (L ⊔ (T : Subgroup G) : Subgroup G) →* MulAut (L ⧸ pCore 2 L) :=
  (quotientAut (pCore 2 L)).comp (L.normalizerMonoidHom.comp
    (inclusion (sup_le L.le_normalizer D.sylow_normalizes_component)))

omit [Finite G] in
theorem augmentationQuotientAction_apply (x : (L ⊔ (T : Subgroup G) : Subgroup G)) (l : L) :
    augmentationQuotientAction D x (QuotientGroup.mk' (pCore 2 L) l) =
      QuotientGroup.mk' (pCore 2 L) (L.normalizerMonoidHom
        ⟨x.val, (sup_le L.le_normalizer D.sylow_normalizes_component) x.property⟩ l) := by
  exact quotientAut_apply_mk (pCore 2 L) _ l

omit [Finite G] in
theorem augmentationCentralAction
    (q : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6))
    (hqL : ∀ l : L, q (inclusion le_sup_left l) =
      (m.quotient (QuotientGroup.mk' (centralCore L) l)).val) (x : (L ⊔ (T : Subgroup G) : Subgroup G)) :
    MulAut.centralQuotientAction (augmentationCentralQuotient D m) (augmentationQuotientAction D x) =
      MulAut.conjNormal (q x) := by
  apply MulEquiv.ext
  intro a
  obtain ⟨b,rfl⟩ := m.quotient.surjective a
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (centralCore L) b
  rw [← augmentationCentralQuotient_apply D m l, MulAut.centralQuotientAction_apply,
    augmentationQuotientAction_apply, augmentationCentralQuotient_apply,
    augmentationCentralQuotient_apply]
  apply Subtype.ext
  let l' := L.normalizerMonoidHom
    ⟨x.val, (sup_le L.le_normalizer D.sylow_normalizes_component) x.property⟩ l
  have he : inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) l' =
      x * inclusion le_sup_left l * x⁻¹ := Subtype.ext rfl
  have hf := congrArg (q) he
  rw [map_mul, map_mul, map_inv, hqL, hqL] at hf
  exact hf


include D m
omit [Finite G] in
private theorem centralCore_le_point (z : V) :
    (centralCore L).map L.subtype ≤
      (L ⊔ (T : Subgroup G)) ⊓ centralizer ({z.val} : Set G) := by
  refine le_inf ((map_subtype_le _).trans le_sup_left) ?_
  rintro _ ⟨l,hl,rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  have hh := m.equivariant l z
  have hlq : QuotientGroup.mk' (centralCore L) l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
  rw [hlq,map_one,OneMemClass.coe_one,map_one,Module.End.one_apply] at hh
  exact (mul_inv_eq_iff_eq_mul.mp
    (congrArg Subtype.val (m.coordinate.injective (Multiplicative.toAdd.injective hh))))

omit [Finite G] in
/-- The actual point radical fixes the center of the component's two-core quotient. -/
theorem augmentation_point_core_fixes_center
    (v : V) (x : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hx : x.val ∈ ((L ⊔ (T : Subgroup G)) ⊓ centralizer ({v.val} : Set G)).pCoreIn 2)
    (z : L ⧸ pCore 2 L) (hz : z ∈ center (L ⧸ pCore 2 L)) :
    augmentationQuotientAction D x z = z := by
  let X := L ⊔ (T : Subgroup G)
  let P := X ⊓ centralizer ({v.val} : Set G)
  let R := P.pCoreIn 2
  let C := (centralCore L).map L.subtype
  let : (centralCore L).Characteristic :=
    inferInstanceAs (Subgroup.centralPreimage (pCore 2 L)).Characteristic
  have hNC : normalizer (L : Set G) ≤ normalizer (C : Set G) :=
    normalizer_le_normalizer_characteristic_image L (centralCore L)
  have hPR : P ≤ normalizer (R : Set G) :=
    P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  have hCQ : C ⊓ R ≤ C.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 P).to_le inf_le_right) inf_le_left
    exact (le_inf C.le_normalizer ((centralCore_le_point D m v).trans hPR)).trans
      inf_normalizer_le_normalizer_inf
  have hCL : C.pCoreIn 2 ≤ L.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes (map_subtype_le _) (L.le_normalizer.trans hNC)
  have hc : ⁅R,C⁆ ≤ L.pCoreIn 2 := by
    apply (le_inf ?_ ?_).trans (hCQ.trans hCL)
    · exact le_normalizer_iff_commutator_le_right.mp
        (((pCoreIn_le 2 P).trans inf_le_left).trans
          ((sup_le L.le_normalizer D.sylow_normalizes_component).trans hNC))
    · exact le_normalizer_iff_commutator_le_left.mp ((centralCore_le_point D m v).trans hPR)
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) z
  have hl : l ∈ centralCore L := hz
  let l' := L.normalizerMonoidHom
    ⟨x.val, (sup_le L.le_normalizer D.sylow_normalizes_component) x.property⟩ l
  have hm : l' * l⁻¹ ∈ pCore 2 L := by
    obtain ⟨a,ha,he⟩ := hc (commutator_mem_commutator hx (mem_map_of_mem L.subtype hl))
    exact (show a = l' * l⁻¹ from Subtype.ext he) ▸ ha
  rw [augmentationQuotientAction_apply]
  apply mul_inv_eq_one.mp
  rw [←map_inv,←map_mul]
  exact (QuotientGroup.eq_one_iff (l' * l⁻¹)).mpr hm

/-- A covered component's point radical has no transposition in its original
five-dimensional augmentation action. -/
theorem covered_augmentation_point_core_no_swap
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (q : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6))
    (hqL : ∀ l : L, q (inclusion le_sup_left l) =
      (m.quotient (QuotientGroup.mk' (centralCore L) l)).val)
    (v : V) (x : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hx : x.val ∈ ((L ⊔ (T : Subgroup G)) ⊓ centralizer ({v.val} : Set G)).pCoreIn 2) :
    ¬ (q x).IsSwap := by
  obtain ⟨j⟩ := GLS3.Chapter5.OddCentralCovers.triple_six_equiv_hexacode
    (augmentationCentralQuotient D m) hc
  intro ht
  let a := augmentationQuotientAction D x
  have hβ := augmentationCentralAction D m q hqL x
  change MulAut.centralQuotientAction _ a = _ at hβ
  have ht2 : (q x)^2 = 1 := by simpa only [ht.orderOf] using pow_orderOf_eq_one (q x)
  have ha2 : a^2 = 1 := by
    apply MulAut.centralQuotientAction_injective (augmentationCentralQuotient D m)
    rw [map_pow,map_one,hβ,←map_pow,ht2,map_one]
  have haout : ∀ b : L ⧸ pCore 2 L, a ≠ MulAut.conj b := by
    intro b hb
    let b' := augmentationCentralQuotient D m (QuotientGroup.mk' (center (L ⧸ pCore 2 L)) b)
    have hh : MulAut.conjNormal (q x) = MulAut.conj b' := by
      rw [←hβ,hb,MulAut.centralQuotientAction_conj]
    have he : q x = b'.val :=
      GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by decide)
        (hh.trans (MulAut.conjNormal_val (h := b')).symm)
    have hs : Equiv.Perm.sign (q x) = 1 := by
      rw [he]
      exact Equiv.Perm.mem_alternatingGroup.mp b'.property
    rw [ht.sign_eq] at hs
    norm_num at hs
  have hinv := Theory.HexEvenExtension.center_inverted_of_hex_model j a ha2 haout
  have hzbot : center (L ⧸ pCore 2 L) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have hfix : a z = z := augmentation_point_core_fixes_center D m v x hx z hz
    have hz2 : z^2 = 1 := by
      have he : z = z⁻¹ := hfix.symm.trans (hinv z hz)
      rw [pow_two]
      calc
        z * z = z⁻¹ * z := congrArg (fun w => w*z) he
        _ = 1 := inv_mul_cancel z
    have hz3 : z^3 = 1 := by
      have hh := pow_card_eq_one' (x := (⟨z,hz⟩ : center (L ⧸ pCore 2 L)))
      rw [hc] at hh
      exact congrArg Subtype.val hh
    rw [pow_succ,hz2,one_mul] at hz3
    exact hz3
  rw [hzbot,card_bot] at hc
  contradiction
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem twoThree_of_two {A : Type*} [Group A] [Finite A]
    (hA : IsPGroup 2 A) : IsPiGroup twoThreePrimes A := by
  obtain ⟨n,hn⟩ := hA.exists_card_eq
  rw [IsPiGroup_iff]
  intro p hp
  rw [hn] at hp
  exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
    (p.property.dvd_of_dvd_pow hp) |>.resolve_left p.property.ne_one)

private theorem twoThree_of_hom {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (f : A →* B) (hB : IsPiGroup twoThreePrimes B)
    (hk : IsPiGroup twoThreePrimes f.ker) : IsPiGroup twoThreePrimes A :=
  IsPiGroup.of_normal_subgroup_and_quotient f.ker (hk.isPiSubgroup _)
    (hB.of_injective (QuotientGroup.kerLift f) (QuotientGroup.kerLift_injective f))

/-- The original augmentation point centralizer remains a {2,3}-group
in the triple-cover row. -/
theorem covered_augmentation_point_twoThree
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hz : z.val ∉ centralizer (L : Set G)) :
    IsPiGroup twoThreePrimes (L ⊓ centralizer ({z.val} : Set G) : Subgroup G) := by
  have hcenter : IsPiGroup twoThreePrimes (center (L ⧸ pCore 2 L)) := by
    rw [IsPiGroup_iff]
    intro p hp
    rw [hc] at hp
    exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp hp |>.resolve_left p.property.ne_one)
  let r : centralCore L →* center (L ⧸ pCore 2 L) :=
    ((QuotientGroup.mk' (pCore 2 L)).comp (centralCore L).subtype).codRestrict _
      (fun x => x.property)
  have hr : r.ker = (pCore 2 L).comap (centralCore L).subtype := by
    ext x
    change (⟨QuotientGroup.mk' (pCore 2 L) x.val,_⟩ : center (L ⧸ pCore 2 L)) = 1 ↔ _
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff _
  have hcore : IsPiGroup twoThreePrimes (centralCore L) := by
    apply twoThree_of_hom r hcenter
    rw [hr]
    exact twoThree_of_two (pCore_isPGroup.comap_of_injective _ (centralCore L).subtype_injective)
  let C := L ⊓ centralizer ({z.val} : Set G)
  let w := (m.coordinate z).toAdd
  let S := BinaryPermutation.SixCoreStabilizer.stabilizer w
  let q : L →* alternatingGroup (Fin 6) :=
    m.quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L))
  have heq (l : L) : q l ∈ S ↔ l.val ∈ centralizer ({z.val} : Set G) := by
    change BinaryPermutation.coreRepresentation (Fin 6)
      (m.quotient (QuotientGroup.mk' (centralCore L) l)).val (m.coordinate z).toAdd =
        (m.coordinate z).toAdd ↔ _
    rw [← m.equivariant l z]
    rw [Multiplicative.toAdd.injective.eq_iff,m.coordinate.injective.eq_iff,Subtype.ext_iff]
    change l.val * z.val * l.val⁻¹ = z.val ↔ _
    rw [mul_inv_eq_iff_eq_mul,mem_centralizer_singleton_iff,eq_comm]
  let k : C →* L := inclusion inf_le_left
  let f : C →* S := (q.comp k).codRestrict S (fun c => (heq (k c)).mpr c.property.2)
  have hker : f.ker = (centralCore L).comap k := by
    ext c
    change (⟨q (k c),_⟩ : S) = 1 ↔ k c ∈ centralCore L
    rw [Subtype.ext_iff]
    change m.quotient (QuotientGroup.mk' (centralCore L) (k c)) = 1 ↔ _
    rw [m.quotient.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff _
  have hk : IsPiGroup twoThreePrimes f.ker := by
    rw [hker]
    let i : (centralCore L).comap k →* centralCore L :=
      (k.comp ((centralCore L).comap k).subtype).codRestrict _ (fun x => x.property)
    apply hcore.of_injective i
    intro x y hh
    apply Subtype.ext
    apply inclusion_injective (show C ≤ L from inf_le_left)
    exact congrArg (fun a : centralCore L => a.val) hh
  have hfix : ¬ ∀ a : alternatingGroup (Fin 6),
      BinaryPermutation.alternatingCoreRepresentation (Fin 6) a w = w := by
    intro h
    exact hz ((m.mem_fixed_iff z).mpr
      ((BinaryPermutation.core_fixed_iff_constant (by simp) w).mp h))
  obtain ⟨e⟩ := BinaryPermutation.SixCoreStabilizer.quotient_equiv w hfix
  have hS : IsPiGroup twoThreePrimes S := by
    apply twoThree_of_hom (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 S)))
    · rw [IsPiGroup_iff]
      intro p hp
      rw [Nat.card_perm,Nat.card_fin] at hp
      rcases p.property.dvd_mul.mp (show p.val ∣ 2*3 from hp) with hp | hp
      · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp hp |>.resolve_left p.property.ne_one)
      · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp hp |>.resolve_left p.property.ne_one)
    · rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
      exact twoThree_of_two pCore_isPGroup
  exact twoThree_of_hom f hS hk

/-- The covered point parabolic is the literal L₁T, with L₁ defined using
O^{3′}, not a two-core or an assumed point-stabilizer identification. -/
theorem covered_augmentation_point_parabolic
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hz : z.val ∉ centralizer (L : Set G)) :
    Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G) =
      (L ⊔ (T : Subgroup G)) ⊓ centralizer ({z.val} : Set G) := by
  rw [Solvable.firstCentralizerResidual_eq,
    ←twoResidual_eq_primeToResidual_three (covered_augmentation_point_twoThree D m hc z hz)]
  exact embedded_pointResidual_sup_sylow T L D.sylow_normalizes_component z.val
    (Solvable.original_sylow_le_centralizer hzT)
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
