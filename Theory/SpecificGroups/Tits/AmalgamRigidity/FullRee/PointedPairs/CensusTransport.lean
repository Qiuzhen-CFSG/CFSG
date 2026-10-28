module
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.PointedPairs.First
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.PointedPairs.SecondEmbedding

/-!
# The common Borel conjugator for binary Ree reflection pairs

The first coordinate endpoint reduces an outside-Borel involution to its
Weyl involution or that involution times the last root. A second-coordinate
conjugator fixed by the first Weyl action commutes with both representatives:
the last root is central in the core. Composing these conjugators therefore
places both original endpoint elements in their specified representatives
with one common Borel element.

All three ambient maps retain the verified original root embedding. The
second-coordinate orbit theorem is the only explicit intermediate input;
`PointedPairs.Census` supplies it from the concrete finite calculation.
Source: the binary Ree local calculation for Aschbacher--Smith F.4.8,
printed p.278, with Shinoda's collected root coordinates (1975), pp.81--83.
-/

@[expose] public section
noncomputable section
namespace Tits.AmalgamRigidity.FullRee.PointedPairs
open ReeTwo FirstRestrictions ParabolicMarkedComparison
open ReeF4.Parabolics.Binary.FixedGeometry
local notation "B" => Tits.ExceptionalParabolics.FullRee.B
local notation "P" => Tits.ExceptionalParabolics.FullRee.first
local notation "Q" => Tits.ExceptionalParabolics.FullRee.second

abbrev firstCoordinateEquiv : E ≃* P := FirstRestrictions.equiv.trans Verified.firstEquiv
abbrev firstAmbient : E →* ReeF4.Model 0 := (P).subtype.comp firstCoordinateEquiv.toMonoidHom
abbrev borelAmbient : SylowModel →* ReeF4.Model 0 := (B).subtype.comp borelEquiv.toMonoidHom
abbrev secondAmbient : SecondModel →* ReeF4.Model 0 := (Q).subtype.comp secondMap

@[simp] theorem firstAmbient_fromS (b : SylowModel) :
    firstAmbient (fromS b) = borelAmbient b := rfl
@[simp] theorem secondAmbient_secondSylow (b : SylowModel) :
    secondAmbient (secondSylow b) = borelAmbient b := by
  change (secondMap (secondSylow b) : ReeF4.Model 0) = _
  rw [secondMap_secondSylow]
  rfl
@[simp] theorem firstAmbient_weyl : firstAmbient (SemidirectProduct.inr FiveFour.r) =
    weylLift 0 .suzuki := by
  change Verified.localMap (SemidirectProduct.inr (Core.complementEquiv FiveFour.r)) = _
  rw [Core.complementEquiv_r]
  exact Verified.localMap_weyl
@[simp] theorem firstAmbient_lastRoot : firstAmbient (SemidirectProduct.inl (Core.root 9)) =
    Ambient.root 9 := Verified.localMap_root 9
@[simp] theorem secondAmbient_reflection :
    secondAmbient (SemidirectProduct.inr (DihedralGroup.sr 0)) = weylLift 0 .linear := by
  change (secondMap (SemidirectProduct.inr (DihedralGroup.sr 0)) : ReeF4.Model 0) = _
  rw [secondMap_reflection]
  rfl
@[simp] theorem borelAmbient_rootOne : borelAmbient SylowModel.rootOne = Ambient.rootOne :=
  SecondExtension.inclusion_rootOne

theorem firstAmbient_representative (e : ZMod 2) :
    firstAmbient (firstRepresentative e) =
      if e = 0 then weylLift 0 .suzuki else Ambient.root 9 * weylLift 0 .suzuki := by
  unfold firstRepresentative
  rw [map_mul, map_pow, map_pow, firstAmbient_lastRoot, firstAmbient_weyl]
  have hv : (e=0 ∧ e.val=0) ∨ (e≠0 ∧ e.val=1) :=
    (by decide : ∀ a : ZMod 2, (a=0 ∧ a.val=0) ∨ (a≠0 ∧ a.val=1)) e
  rcases hv with ⟨he,hv⟩ | ⟨he,hv⟩
  · rw [if_pos he, hv, pow_zero, one_mul]
  · rw [if_neg he, hv, pow_one]

theorem borelAmbient_mem (b : SylowModel) : borelAmbient b ∈ B := (borelEquiv b).property

theorem borelAmbient_range : borelAmbient.range = B := by
  ext x
  constructor
  · rintro ⟨b, rfl⟩; exact borelAmbient_mem b
  · intro hx
    exact ⟨borelEquiv.symm ⟨x,hx⟩, congrArg Subtype.val (borelEquiv.apply_symm_apply ⟨x,hx⟩)⟩

theorem firstRepresentative_commutes (g : Core) (hg : Core.r g = g) (e : ZMod 2) :
    (fromS (SemidirectProduct.inl g)) * firstRepresentative e *
      (fromS (SemidirectProduct.inl g))⁻¹ = firstRepresentative e := by
  have hr : Commute (SemidirectProduct.inl g : E) (SemidirectProduct.inr FiveFour.r) := by
    change (SemidirectProduct.inl g : E) * SemidirectProduct.inr FiveFour.r =
      SemidirectProduct.inr FiveFour.r * SemidirectProduct.inl g
    apply SemidirectProduct.ext
    · change g * 1 = 1 * Core.complementAction FiveFour.r g
      rw [Core.complementAction_r, hg, mul_one, one_mul]
    · simp
  have hz : Commute g (Core.root 9) := by
    change Core.mul g (Core.root 9) = Core.mul (Core.root 9) g
    apply Core.ext <;> simp [Core.mul, Core.root, Core.ofCoords]
    ring
  have h := (hz.pow_right e.val).map (SemidirectProduct.inl : Core →* E)
  have hc := h.mul_right hr
  change (SemidirectProduct.inl g : E) * _ * (SemidirectProduct.inl g)⁻¹ = _
  exact hc.mul_inv_cancel


theorem ambient_first_conjugate (x : ReeF4.Model 0) (hx : x ∈ P)
    (hx2 : x^2=1) (hn : x ∉ B) :
    ∃ b : SylowModel, ∃ e : ZMod 2,
      x = borelAmbient b *
        (if e=0 then weylLift 0 .suzuki else Ambient.root 9 * weylLift 0 .suzuki) *
        (borelAmbient b)⁻¹ := by
  let a := firstCoordinateEquiv.symm ⟨x,hx⟩
  have ha : firstAmbient a = x :=
    congrArg Subtype.val (firstCoordinateEquiv.apply_symm_apply ⟨x,hx⟩)
  have hi : Function.Injective firstAmbient :=
    (P).subtype_injective.comp firstCoordinateEquiv.injective
  have h2 : a^2=1 := hi (by rw [map_pow, map_one, ha, hx2])
  have hnot : a ∉ fromS.range := by
    rintro ⟨b,hb⟩
    apply hn
    rw [← ha, ← hb, firstAmbient_fromS]
    exact borelAmbient_mem b
  obtain ⟨b,e,he⟩ := first_involution_conjugate a h2 hnot
  refine ⟨b,e, ?_⟩
  simpa only [map_mul, map_inv, firstAmbient_fromS, firstAmbient_representative, ha] using
    congrArg firstAmbient he

theorem ambient_first_fixed (g : Core) (hg : Core.r g = g) (e : ZMod 2) :
    borelAmbient (SemidirectProduct.inl g) *
      (if e=0 then weylLift 0 .suzuki else Ambient.root 9 * weylLift 0 .suzuki) *
      (borelAmbient (SemidirectProduct.inl g))⁻¹ =
      (if e=0 then weylLift 0 .suzuki else Ambient.root 9 * weylLift 0 .suzuki) := by
  simpa only [map_mul, map_inv, firstAmbient_fromS, firstAmbient_representative] using
    congrArg firstAmbient (firstRepresentative_commutes g hg e)

def secondRepFormula (e : ZMod 2) : SecondModel :=
  if e=0 then SemidirectProduct.inr (DihedralGroup.sr 0)
  else (secondSylow SylowModel.rootOne)⁻¹ * SemidirectProduct.inr (DihedralGroup.sr 0) *
    secondSylow SylowModel.rootOne

theorem secondAmbient_formula (e : ZMod 2) : secondAmbient (secondRepFormula e) =
    if e=0 then weylLift 0 .linear else
      Ambient.rootOne⁻¹ * weylLift 0 .linear * Ambient.rootOne := by
  unfold secondRepFormula
  split <;> simp only [map_mul, map_inv, secondAmbient_reflection,
    secondAmbient_secondSylow, borelAmbient_rootOne]

theorem ambient_second_conjugate
    (hsecond : ∀ y : SecondModel, y^2=1 → y ∉ secondSylow.range →
      ∃ g : Core, Core.r g = g ∧ ∃ e : ZMod 2,
        y = secondSylow (SemidirectProduct.inl g) * secondRepFormula e *
          (secondSylow (SemidirectProduct.inl g))⁻¹)
    (y : ReeF4.Model 0) (hy : y ∈ Q) (hy2 : y^2=1) (hn : y ∉ B) :
    ∃ g : Core, Core.r g = g ∧ ∃ e : ZMod 2,
      y = borelAmbient (SemidirectProduct.inl g) *
        (if e=0 then weylLift 0 .linear else
          Ambient.rootOne⁻¹ * weylLift 0 .linear * Ambient.rootOne) *
        (borelAmbient (SemidirectProduct.inl g))⁻¹ := by
  let a := secondEquiv.symm ⟨y,hy⟩
  have ha : secondAmbient a = y :=
    congrArg Subtype.val (secondEquiv.apply_symm_apply ⟨y,hy⟩)
  have hi : Function.Injective secondAmbient :=
    (Q).subtype_injective.comp secondMap_bijective.1
  have h2 : a^2=1 := hi (by rw [map_pow, map_one, ha, hy2])
  have hnot : a ∉ secondSylow.range := by
    rintro ⟨b,hb⟩
    apply hn
    rw [← ha, ← hb, secondAmbient_secondSylow]
    exact borelAmbient_mem b
  obtain ⟨g,hg,e,he⟩ := hsecond a h2 hnot
  refine ⟨g,hg,e, ?_⟩
  simpa only [map_mul, map_inv, secondAmbient_secondSylow, secondAmbient_formula, ha] using
    congrArg secondAmbient he


theorem reflection_pair_conjugate_of_second_census
    (hsecond : ∀ y : SecondModel, y^2=1 → y ∉ secondSylow.range →
      ∃ g : Core, Core.r g = g ∧ ∃ e : ZMod 2,
        y = secondSylow (SemidirectProduct.inl g) * secondRepFormula e *
          (secondSylow (SemidirectProduct.inl g))⁻¹)
    (x y : ReeF4.Model 0) (hx : x ∈ P) (hy : y ∈ Q)
    (hnx : x ∉ B) (hny : y ∉ B) (hx2 : x^2=1) (hy2 : y^2=1) :
    ∃ b : B, ∃ i j : Bool,
      x = b * (if i then Ambient.root 9 * weylLift 0 .suzuki else weylLift 0 .suzuki) *
        (b : ReeF4.Model 0)⁻¹ ∧
      y = b * (if j then Ambient.rootOne⁻¹ * weylLift 0 .linear * Ambient.rootOne
        else weylLift 0 .linear) * (b : ReeF4.Model 0)⁻¹ := by
  obtain ⟨b,e,he⟩ := ambient_first_conjugate x hx hx2 hnx
  let y' := (borelAmbient b)⁻¹ * y * borelAmbient b
  have hb : borelAmbient b ∈ B := borelAmbient_mem b
  have hbq : borelAmbient b ∈ Q := ExceptionalParabolics.FullRee.borel_le_second hb
  have hy' : y' ∈ Q := (Q).mul_mem ((Q).mul_mem ((Q).inv_mem hbq) hy) hbq
  have hy'2 : y'^2=1 := by
    dsimp only [y']
    calc
      _ = (borelAmbient b)⁻¹ * y^2 * borelAmbient b := by simp only [pow_two]; group
      _ = 1 := by rw [hy2]; group
  have hny' : y' ∉ B := by
    intro h
    apply hny
    have hh := (B).mul_mem ((B).mul_mem hb h) ((B).inv_mem hb)
    convert hh using 1
    dsimp only [y']
    group
  obtain ⟨g,hg,f,hf⟩ := ambient_second_conjugate hsecond y' hy' hy'2 hny'
  refine ⟨borelEquiv (b * SemidirectProduct.inl g), decide (e≠0), decide (f≠0), ?_, ?_⟩
  · have hr := ambient_first_fixed g hg e
    have hc : x = borelAmbient (b * SemidirectProduct.inl g) *
        (if e=0 then weylLift 0 .suzuki else Ambient.root 9 * weylLift 0 .suzuki) *
        (borelAmbient (b * SemidirectProduct.inl g))⁻¹ := by
      rw [map_mul, mul_inv_rev]
      calc
        x = borelAmbient b *
            (borelAmbient (SemidirectProduct.inl g) *
              (if e=0 then weylLift 0 .suzuki else Ambient.root 9 * weylLift 0 .suzuki) *
              (borelAmbient (SemidirectProduct.inl g))⁻¹) * (borelAmbient b)⁻¹ := by rw [hr]; exact he
        _ = _ := by group
    change x = borelAmbient (b * SemidirectProduct.inl g) * _ *
      (borelAmbient (b * SemidirectProduct.inl g))⁻¹
    by_cases h : e=0 <;> simpa only [h, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
      if_false, not_false_eq_true, decide_true, if_true] using hc
  · have hc : y = borelAmbient (b * SemidirectProduct.inl g) *
        (if f=0 then weylLift 0 .linear else
          Ambient.rootOne⁻¹ * weylLift 0 .linear * Ambient.rootOne) *
        (borelAmbient (b * SemidirectProduct.inl g))⁻¹ := by
      rw [map_mul, mul_inv_rev]
      calc
        y = borelAmbient b * y' * (borelAmbient b)⁻¹ := by dsimp only [y']; group
        _ = _ := by rw [hf]; group
    change y = borelAmbient (b * SemidirectProduct.inl g) * _ *
      (borelAmbient (b * SemidirectProduct.inl g))⁻¹
    by_cases h : f=0 <;> simpa only [h, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
      if_false, not_false_eq_true, decide_true, if_true] using hc

end Tits.AmalgamRigidity.FullRee.PointedPairs
