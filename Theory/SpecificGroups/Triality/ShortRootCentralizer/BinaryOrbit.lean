module
public import Theory.SpecificGroups.Triality.ShortRootCentralizer.BinaryNonsplit
public import Theory.SpecificGroups.Triality.ArmsOrbit
public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.CentralRootSquare.ParabolicAction.Basic
public import Theory.SpecificGroups.Triality.ParabolicCoreExtraspecial

/-!
# The characteristic short-root class in the binary central parabolic

The derived radical is the kernel of its first two cubic coordinates; its
center is the zero third-coordinate part. Torus scaling moves any nonzero
third coordinate to any other, and the nondegenerate trace pairing supplies
both central coordinates by conjugation. Thus the derived radical outside
its center is one class of the full parabolic, preserved by every endpoint
automorphism through the characteristic two-core.

This supplies the short-centralizer supplement in the cubic extension of
Aschbacher--Smith F.4.42 and 14.2.18, printed pp.295,987
(`refs/quasithin.pdf`). The literal original-endpoint application is
Chapter14/Section02/EightLargeParabolic/ShortExtension. All conjugators lie
in the actual native central parabolic.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace Triality.Standard.ShortRootCentralizer.BinaryOrbit
open Parabolics RadicalCoordinates RadicalCoordinates.Centers RadicalCoordinates.LeviCommutators
open Parabolics.CentralRootSquare Parabolics.CentralRootSquare.ElementaryImage
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "hp2" => binaryParameters_prime 1 Nat.zero_lt_one
local notation "Q" => radical P Node.central

theorem higher_val (a : ExtensionField P) :
    (coordinates P hp2 (![0,0,a],0)).val = short P hp2 2 a := by
  rw [coordinates_val,rootElement_factorization]
  simp [extendOrbit]

private theorem factor_of_first_zero (x : Q) (hx : firstLayer P hp2 x = 0) :
    ∃ a b : fixedField P, x.val = short P hp2 2 (thirdLayer P hp2 x) *
      (long P hp2 1 a * long P hp2 2 b) := by
  obtain ⟨v,rfl⟩ := (coordinates P hp2).surjective x
  rw [firstLayer_coordinates] at hx
  have h0 : v.1 0 = 0 := congrArg Prod.fst hx
  have h1 : v.1 1 = 0 := congrArg Prod.snd hx
  refine ⟨v.2 0,v.2 1,?_⟩
  rw [coordinates_val,rootElement_factorization,thirdLayer_coordinates]
  simp [extendOrbit,h0,h1,mul_assoc]

private theorem plane_le_derived : plane P ≤ ⁅Q,Q⁆ :=
  (plane_le_shortRadical_commutator (1 : ExtensionField P)).trans
    (commutator_mono inf_le_left inf_le_left)

private theorem higher_coefficient_mem_derived (a b : ExtensionField P) :
    short P hp2 2 (higherCoefficient P a b) ∈ ⁅Q,Q⁆ := by
  let x := coordinates P hp2 (![a,0,0],0)
  let y := coordinates P hp2 (![0,b,0],0)
  have hfirst := firstLayer_commutator P hp2 x y
  obtain ⟨d,e,he⟩ := factor_of_first_zero ⁅x,y⁆ hfirst
  have hh : thirdLayer P hp2 ⁅x,y⁆ = higherCoefficient P a b := by
    rw [thirdLayer_commutator]
    dsimp only [x, y]
    rw [firstLayer_coordinates, firstLayer_coordinates]
    simp [higherCoefficient, -fieldFrobenius_apply]
  rw [hh] at he
  have hc : (⁅x,y⁆ : Q).val ∈ ⁅Q,Q⁆ := by
    change ⁅x.val,y.val⁆ ∈ ⁅Q,Q⁆
    exact commutator_mem_commutator x.property y.property
  have hp : long P hp2 1 d * long P hp2 2 e ∈ ⁅Q,Q⁆ :=
    plane_le_derived ((plane_mem_iff P hp2 _).mpr ⟨d,e,rfl⟩)
  rw [he] at hc
  exact (mul_mem_cancel_right hp).mp hc

theorem higher_mem_derived (a : ExtensionField P) : short P hp2 2 a ∈ ⁅Q,Q⁆ := by
  obtain ⟨s,t,u,rfl⟩ := exists_sum_higherCoefficient P hp2 a
  rw [short_add]
  exact mul_mem (higher_coefficient_mem_derived s t) (higher_coefficient_mem_derived 1 u)

/-- The derived two-core is exactly the zero first-layer subgroup. -/
theorem mem_derived_iff (x : Q) : x ∈ _root_.commutator Q ↔ firstLayer P hp2 x = 0 := by
  let f := firstLayerHom P hp2 (firstLayer_mul P hp2)
  constructor
  · intro hx
    exact (Abelianization.commutator_subset_ker f) hx
  · intro hx
    have he := map_subtype_commutator Q
    have hx' : x.val ∈ ⁅Q,Q⁆ := by
      obtain ⟨a,b,hxv⟩ := factor_of_first_zero x hx
      rw [hxv]
      exact mul_mem (higher_mem_derived _) (plane_le_derived
        ((plane_mem_iff P hp2 _).mpr ⟨a,b,rfl⟩))
    rw [←he] at hx'
    obtain ⟨y,hy,hyx⟩ := hx'
    exact (Subtype.ext hyx : y = x) ▸ hy

/-- The center is exactly the zero third-layer part of the derived core. -/
theorem mem_center_iff (x : Q) (hx : x ∈ _root_.commutator Q) :
    x ∈ center Q ↔ thirdLayer P hp2 x = 0 := by
  constructor
  · intro hc
    rw [←planeHom_range P hp2] at hc
    obtain ⟨a,rfl⟩ := hc
    change thirdLayer P hp2 (coordinates P hp2 (0,a.toAdd)) = 0
    rw [thirdLayer_coordinates]
    rfl
  · intro hc
    obtain ⟨v,rfl⟩ := (coordinates P hp2).surjective x
    have hf := (mem_derived_iff _).mp hx
    rw [firstLayer_coordinates] at hf
    have h0 : v.1 0 = 0 := congrArg Prod.fst hf
    have h1 : v.1 1 = 0 := congrArg Prod.snd hf
    rw [thirdLayer_coordinates] at hc
    have h2 : v.1 2 = 0 := hc
    rw [←planeHom_range P hp2]
    refine ⟨Multiplicative.ofAdd v.2,?_⟩
    change coordinates P hp2 (0,v.2) = coordinates P hp2 v
    congr 1
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [h0,h1,h2]
    · rfl

private theorem torus_mem (t : (ExtensionField P)ˣ) :
    torusActor P hp2 .arms t ∈ parabolic P .central := by
  apply (ConcreteBruhat.torus_le_borel P).trans (borel_le_parabolic P .central)
  refine ⟨torusElementary P hp2 .arms t, ?_, rfl⟩
  change elementaryInclusion P _ ∈ ConcreteBruhat.splitTorus P
  rw [torusElementary_arms_val]
  exact mul_mem (mul_mem (subset_closure ⟨0,t,rfl⟩)
    (subset_closure ⟨2,_,rfl⟩)) (subset_closure ⟨3,_,rfl⟩)

private theorem torus_short_two (t : (ExtensionField P)ˣ) (d : ExtensionField P) :
    torusActor P hp2 .arms t * short P hp2 2 d * (torusActor P hp2 .arms t)⁻¹ =
      short P hp2 2 (t.val⁻¹*d) := by
  have hscale : t.val * fieldFrobenius P t.val /
      fieldFrobenius P (fieldFrobenius P t.val)=t.val⁻¹ := by
    change t.val * t.val ^ 2 / ((t.val ^ 2) ^ 2) = t.val⁻¹
    field_simp
  have hh := (torus_arms_short_two_conjugate P hp2 t d).trans
    (congrArg (fun s : ExtensionField P => shortSplit P 2 (s*d)) hscale)
  have he : torusElementary P hp2 .arms t * shortElementary P hp2 2 d *
      (torusElementary P hp2 .arms t)⁻¹ = shortElementary P hp2 2 (t.val⁻¹*d) := by
    apply elementaryInclusion_injective P
    simpa only [map_mul,map_inv,shortElementary_val] using hh
  simpa only [LeviCommutators.torusActor,short,map_mul,map_inv] using congrArg (toCarrier P) he

private theorem first_higher_commutator (a b c : ExtensionField P) :
    ⁅(coordinates P hp2 (![a,b,0],0)).val,short P hp2 2 c⁆ =
      long P hp2 1 (armsPairing P a c) * long P hp2 2 (armsPairing P b c) := by
  let k := coordinates P hp2 (![0,0,c],0)
  have hk : firstLayer P hp2 k = 0 := by rw [firstLayer_coordinates]; rfl
  have he := congrArg Subtype.val
    (commutator_of_firstLayer_zero P hp2 (coordinates P hp2 (![a,b,0],0)) k hk)
  have hh := (map_commutatorElement (radical P .central).subtype
    (coordinates P hp2 (![a,b,0],0)) k).symm.trans he
  change ⁅(coordinates P hp2 (![a,b,0],0)).val,k.val⁆ = _ at hh
  rw [show k.val = short P hp2 2 c from higher_val c] at hh
  have hh' : ⁅(coordinates P hp2 (![a,b,0],0)).val,short P hp2 2 c⁆ =
      (coordinates P hp2 (0,![armsPairing P a c,armsPairing P b c])).val := by
    simpa only [firstLayer,thirdLayer,Equiv.symm_apply_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,k] using hh
  exact hh'.trans (planeHom_val P hp2 (Multiplicative.ofAdd
    ![armsPairing P a c,armsPairing P b c]))

/-- The noncentral derived radical is a single class under the actual parabolic. -/
theorem exists_conjugator (d : ExtensionField P) (hd : d ≠ 0)
    (x : Q) (hx : x ∈ _root_.commutator Q) (hn : x ∉ center Q) :
    ∃ g : parabolic P .central, g.val * short P hp2 2 d * g.val⁻¹ = x.val := by
  let c := thirdLayer P hp2 x
  have hc : c ≠ 0 := fun he => hn ((mem_center_iff x hx).mpr he)
  obtain ⟨a,b,hxv⟩ := factor_of_first_zero x ((mem_derived_iff x).mp hx)
  obtain ⟨v,hv⟩ := armsPairing_surjective_left P hp2 c hc a
  obtain ⟨w,hw⟩ := armsPairing_surjective_left P hp2 c hc b
  change armsPairing P v c = a at hv
  change armsPairing P w c = b at hw
  let u := coordinates P hp2 (![v,w,0],0)
  let t : (ExtensionField P)ˣ := Units.mk0 (d/c) (div_ne_zero hd hc)
  have ht : t.val⁻¹*d=c := by dsimp [t]; field_simp
  have hcomm : ⁅u.val,short P hp2 2 c⁆ = long P hp2 1 a * long P hp2 2 b := by
    rw [first_higher_commutator,hv,hw]
  have hplane := plane_le_centralizer P hp2 c
    ((plane_mem_iff P hp2 _).mpr ⟨a,b,rfl⟩)
  have hm := mem_centralizer_singleton_iff.mp hplane
  refine ⟨⟨u.val * torusActor P hp2 .arms t,
    mul_mem (radical_le_parabolic P .central u.property) (torus_mem t)⟩,?_⟩
  change (u.val * torusActor P hp2 .arms t) * short P hp2 2 d *
    (u.val * torusActor P hp2 .arms t)⁻¹ = _
  calc
    _ = u.val * (torusActor P hp2 .arms t * short P hp2 2 d *
        (torusActor P hp2 .arms t)⁻¹) * u.val⁻¹ := by group
    _ = u.val * short P hp2 2 c * u.val⁻¹ := by rw [torus_short_two,ht]
    _ = ⁅u.val,short P hp2 2 c⁆ * short P hp2 2 c := by group
    _ = x.val := by rw [hcomm,hm]; exact hxv.symm

/-- Every radical automorphism preserves this parabolic class. -/
theorem automorphism_conjugate (f : MulAut Q) (d : ExtensionField P) (hd : d ≠ 0) :
    ∃ g : parabolic P .central, g.val * short P hp2 2 d * g.val⁻¹ =
      (f (coordinates P hp2 (![0,0,d],0))).val := by
  let x := coordinates P hp2 (![0,0,d],0)
  have hx : x ∈ _root_.commutator Q := by
    apply (mem_derived_iff x).mpr
    rw [firstLayer_coordinates]
    rfl
  have hn : x ∉ center Q := by
    intro hn
    have hz := (mem_center_iff x hx).mp hn
    rw [thirdLayer_coordinates] at hz
    exact hd hz
  apply exists_conjugator d hd
  · exact characteristic_iff_le_comap.mp (inferInstance :
      (_root_.commutator Q).Characteristic) f hx
  · intro hc
    exact hn (characteristic_iff_comap_le.mp (inferInstance :
      (center Q).Characteristic) f hc)

/-- Automorphisms of the full endpoint preserve the pinned short-root class. -/
theorem parabolic_automorphism_conjugate (f : MulAut (parabolic P .central))
    (d : ExtensionField P) (hd : d ≠ 0)
    (s : parabolic P .central) (hs : s.val = short P hp2 2 d) : IsConj s (f s) := by
  let E := parabolicTwoCoreEquivRadical P hp2 Node.central
  let fQ := E.symm.trans ((MulAut.characteristic (pCore 2 (parabolic P .central))) f) |>.trans E
  let x := coordinates P hp2 (![0,0,d],0)
  have hE (a : pCore 2 (parabolic P .central)) : (E a).val = a.val.val := rfl
  have hpre : (E.symm x).val = s := by
    apply Subtype.ext
    exact (hE (E.symm x)).symm.trans
      ((congrArg Subtype.val (E.apply_symm_apply x)).trans ((higher_val d).trans hs.symm))
  obtain ⟨g,hg⟩ := automorphism_conjugate fQ d hd
  apply isConj_iff.mpr
  refine ⟨g,Subtype.ext ?_⟩
  change g.val * s.val * g.val⁻¹ = (f s).val
  rw [hs]
  apply hg.trans
  change (f ((E.symm x).val)).val = (f s).val
  rw [hpre]

/-- The long-root plane is characteristic in the full central endpoint. -/
theorem parabolic_automorphism_preserves_plane (f : MulAut (parabolic P .central))
    (x : parabolic P .central) (hx : x.val ∈ plane P) : (f x).val ∈ plane P := by
  let E := parabolicTwoCoreEquivRadical P hp2 Node.central
  let fQ := E.symm.trans ((MulAut.characteristic (pCore 2 (parabolic P .central))) f) |>.trans E
  obtain ⟨q,hq,hqx⟩ := hx
  have hE (a : pCore 2 (parabolic P .central)) : (E a).val = a.val.val := rfl
  have hpre : (E.symm q).val = x := by
    apply Subtype.ext
    exact (hE (E.symm q)).symm.trans
      ((congrArg Subtype.val (E.apply_symm_apply q)).trans hqx)
  refine ⟨fQ q,characteristic_iff_le_comap.mp (inferInstance : (center Q).Characteristic) fQ hq,?_⟩
  change (f ((E.symm q).val)).val = (f x).val
  rw [hpre]


end Triality.Standard.ShortRootCentralizer.BinaryOrbit
