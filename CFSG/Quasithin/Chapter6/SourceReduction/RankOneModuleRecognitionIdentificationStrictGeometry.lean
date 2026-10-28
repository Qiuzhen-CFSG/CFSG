module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictPairs
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityAction
public import Theory.GroupTheory.PGroup.SmallFrattiniLinearForms
public import Theory.Frattini.OmegaProducts

/-!
# The actual extraspecial factor and commutator symplectic space

The elementary conjugate generators and earlier commutator bound imply
Φ(U) ≤ ⟨z⟩. Noncommutativity from the quaternion pair gives equality.
The small-Frattini construction then produces an extraspecial factor
inside U, generating U with its center and sharing the marked line.

The same actual quotient U/Z(U) carries the commutator alternating form.
Its radical is zero and every automorphism of U preserves it. Restricting
the quotient map to the embedded quaternion pair gives at least sixteen
quotient elements, hence symplectic dimension at least four. The form's
value on two quotient representatives is their actual commutator marked
in the binary Frattini line.

Source: Aschbacher--Smith, 6.2.15 and the setup preceding 6.2.16,
printed pp.688--689, with the intrinsic construction also used in 12.8.8.
The later crossing geometry and strict-branch elimination remain separate
steps of this task.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
variable {κ : GroupClass.{u}} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The elementary conjugate generators and the earlier commutator bound put
all of the Frattini subgroup in the marked central line. -/
theorem LocalAnalysis.closure_frattini_le_line
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) :
    let U := sourceClosure (T : Subgroup G) L R z
    (frattini U).map U.subtype ≤ zpowers z := by
  let H := centralizer ({z} : Set G)
  let C := equalityClosure (T : Subgroup G) L R z
  let U := sourceClosure (T : Subgroup G) L R z
  let e : C ≃* U := C.equivMapOfInjective H.subtype H.subtype_injective
  have hCp : IsPGroup 2 C := by
    have hu := (H.isPGroup_pCoreIn 2).to_le A.closure_le_core
    exact hu.of_equiv e.symm
  have hphi := frattini_le_of_elementary_quotient hCp
    ((equalityLine z).subgroupOf C)
    (A.equalityVectorQuotient_elementary h611.ZS_elementary
      (inf_le_left.trans (layer_le_involution_centralizer h611 hz)))
  change (frattini U).map U.subtype ≤ zpowers z
  rw [← frattini_map_equiv e, map_map]
  rintro x ⟨c, hc, rfl⟩
  exact hphi hc

/-- In the strict branch, the ambient image of the actual Frattini subgroup
is exactly the marked involution line. -/
theorem LocalAnalysis.strict_closure_frattini_eq_line
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    let U := sourceClosure (T : Subgroup G) L R z
    (frattini U).map U.subtype = zpowers z ∧ Nat.card (frattini U) = 2 := by
  let U := sourceClosure (T : Subgroup G) L R z
  have htwo : IsPGroup 2 U :=
    ((centralizer ({z} : Set G)).isPGroup_pCoreIn 2).to_le A.closure_le_core
  let : Fact (IsPGroup 2 U) := ⟨htwo⟩
  have hle := A.closure_frattini_le_line h611 hz
  have hd := card_dvd_of_le hle
  rw [card_subtype, Nat.card_zpowers, horder] at hd
  have hc : Nat.card (frattini U) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hc | hc
    · have hbot : frattini U = ⊥ := card_eq_one.mp hc
      have he : IsElementaryAbelian 2 U := frattini_eq_bot_iff_isElementaryAbelian.mp hbot
      exact (A.strict_closure_noncommutative h611 hnatural hz horder hstrict
        he.toIsMulCommutative).elim
    · exact hc
  exact ⟨eq_of_le_of_card_ge hle (by rw [card_subtype, hc, Nat.card_zpowers, horder]), hc⟩

/-- Source 6.2.15(1), the actual extraspecial factor with its central product
and marked common center. Width bounds are supplied separately. -/
theorem LocalAnalysis.strict_extraspecial_factor
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    let U := sourceClosure (T : Subgroup G) L R z
    ∃ F : Subgroup U, IsExtraspecial 2 F ∧ F ⊔ center U = ⊤ ∧
      ((center F).map F.subtype).map U.subtype = zpowers z := by
  let U := sourceClosure (T : Subgroup G) L R z
  have hp : IsPGroup 2 U :=
    ((centralizer ({z} : Set G)).isPGroup_pCoreIn 2).to_le A.closure_le_core
  obtain ⟨hline, hcard⟩ := A.strict_closure_frattini_eq_line h611 hnatural hz horder hstrict
  obtain ⟨F, hF, hgen, hphi⟩ := hp.exists_extraspecial_factor_of_frattini_card_two hcard
    (A.strict_closure_noncommutative h611 hnatural hz horder hstrict)
  let := hF
  refine ⟨F, hF, hgen, ?_⟩
  rw [← IsExtraspecial.frattini_eq_center (p := 2), hphi]
  exact hline



/-- The embedded quaternion pair forces the central quotient of U to have
at least sixteen elements, hence the extraspecial width is at least two. -/
theorem LocalAnalysis.strict_central_quotient_card_ge_sixteen
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    let U := sourceClosure (T : Subgroup G) L R z
    16 ≤ Nat.card (U ⧸ center U) := by
  let U := sourceClosure (T : Subgroup G) L R z
  obtain ⟨g, hg, hp⟩ := A.exists_non_two_layer_pair h611 hnatural hz
  let J := layer L R ⊔ (layer L R).map (MulAut.conj g).toMonoidHom
  obtain ⟨⟨d⟩, _, _, hPU, _⟩ := A.strict_pair_core h611 hnatural hz hstrict hg hp
  let D := (J.pCoreIn 2).subgroupOf U
  let e : D ≃* pCore 2 J := (subgroupOfEquivOfLe hPU).trans
    ((pCore 2 J).equivMapOfInjective J.subtype J.subtype_injective).symm
  have hD : Nat.card D = 32 := (Nat.card_congr e.toEquiv).trans d.card
  have hDC : Nat.card (center D) = 2 := (Nat.card_congr (centerCongr e).toEquiv).trans d.center_card
  have hc : Nat.card (center U ⊓ D : Subgroup U) ≤ 2 := by
    let i : (center U ⊓ D : Subgroup U) → center D := fun x =>
      ⟨⟨x.val, x.property.2⟩, mem_center_iff.mpr
        (fun y => Subtype.ext (mem_center_iff.mp x.property.1 y))⟩
    have hi : Function.Injective i := by
      intro x y h
      exact Subtype.ext (congrArg (fun v : center D => v.val.val) h)
    exact (Nat.card_le_card_of_injective i hi).trans hDC.le
  have hprod := relIndex_mul_relIndex (⊥ : Subgroup U) (center U ⊓ D) D bot_le inf_le_right
  rw [relIndex_bot_left, relIndex_bot_left, hD, inf_relIndex_right] at hprod
  have hr := relIndex_ker D (QuotientGroup.mk' (center U))
  rw [QuotientGroup.ker_mk'] at hr
  rw [hr] at hprod
  have hcard : 16 ≤ Nat.card (D.map (QuotientGroup.mk' (center U))) := by
    nlinarith [Nat.mul_le_mul_right (Nat.card (D.map (QuotientGroup.mk' (center U)))) hc]
  exact hcard.trans (Nat.card_le_card_of_injective _
    (D.map (QuotientGroup.mk' (center U))).subtype_injective)

/-- The commutator symplectic space on the literal central quotient. The
form is evaluated through the marked Frattini line and every actual
subgroup automorphism preserves it. -/
theorem LocalAnalysis.strict_symplectic_geometry
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    let U := sourceClosure (T : Subgroup G) L R z
    ∃ he : IsElementaryAbelian 2 (U ⧸ center U),
      let := he
      ∃ e : frattini U ≃* Multiplicative (ZMod 2),
      ∃ B : LinearMap.BilinForm (ZMod 2) (Additive (U ⧸ center U)),
        B.IsAlt ∧ B.Nondegenerate ∧ 4 ≤ Module.finrank (ZMod 2) (Additive (U ⧸ center U)) ∧
        (∀ x y : U,
          ∃ c : frattini U, (c : U) = ⁅x, y⁆ ∧
          B (Additive.ofMul (QuotientGroup.mk' (center U) x))
            (Additive.ofMul (QuotientGroup.mk' (center U) y)) = (e c).toAdd) ∧
        ∀ (a : MulAut U) (x y : U ⧸ center U),
          B (Additive.ofMul (quotientAut (center U) a x))
            (Additive.ofMul (quotientAut (center U) a y)) =
          B (Additive.ofMul x) (Additive.ofMul y) := by
  let U := sourceClosure (T : Subgroup G) L R z
  have hp : IsPGroup 2 U :=
    ((centralizer ({z} : Set G)).isPGroup_pCoreIn 2).to_le A.closure_le_core
  have hc := (A.strict_closure_frattini_eq_line h611 hnatural hz horder hstrict).2
  let he := SmallFrattini.centralElementary hp hc
  let := he
  refine ⟨he, SmallFrattini.binaryMark hc, SmallFrattini.centralBilinearForm hp hc,
    SmallFrattini.centralBilinearForm_isAlt hp hc,
    SmallFrattini.centralBilinearForm_nondegenerate hp hc, ?_, ?_, ?_⟩
  · change 4 ≤ Module.finrank (ZMod 2) (Additive (U ⧸ center U))
    have hb := A.strict_central_quotient_card_ge_sixteen h611 hnatural hz hstrict
    let := Fintype.ofFinite (Additive (U ⧸ center U))
    have hcard := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive (U ⧸ center U))
    simp only [← Nat.card_eq_fintype_card] at hcard
    have hsame : Nat.card (Additive (U ⧸ center U)) = Nat.card (U ⧸ center U) := rfl
    have hf : Nat.card (ZMod 2) = 2 := by rw [Nat.card_eq_fintype_card, ZMod.card]
    rw [hsame, hf] at hcard
    change 16 ≤ Nat.card (U ⧸ center U) at hb
    rw [hcard] at hb
    by_contra hn
    have hlt : Module.finrank (ZMod 2) (Additive (U ⧸ center U)) < 4 := by omega
    have := Nat.pow_lt_pow_right (by decide : 1 < 2) hlt
    norm_num at this
    omega
  · intro x y
    refine ⟨SmallFrattini.centralCommutator hp (QuotientGroup.mk' (center U) x)
      (QuotientGroup.mk' (center U) y), SmallFrattini.centralCommutator_apply_mk hp x y, ?_⟩
    exact SmallFrattini.centralBilinearForm_apply hp hc _ _
  · exact SmallFrattini.centralBilinearForm_invariant hp hc

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
