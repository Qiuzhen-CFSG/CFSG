module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixScalarResidual
public import Theory.Representation.HexacodeAction.CentralCharacter
public import CFSG.Quasithin.ChapterI.Section06To08.Basic
public import Theory.GroupTheory.DisjointConjugateCenter
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# The original Held field point is a TI-subgroup

The literal scalar residual X maps onto the entire central cubic. Its
marked field character therefore makes X transitive on the three
nonidentity elements of the actual point Vt. The original centralizer
H=C_G(t) normalizes the conjugate span B and hence its center Vt.
Scalar transport gives the same centralizer bound at every nonidentity
point, and I.6.1(1) proves TI. No fusion or TI premise is retained.

Source: Aschbacher--Smith 12.7.7, printed p.841, and I.6.1(1).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

private theorem scalar_conjugate (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (x : K)
    (hx : a.groupEquiv (QuotientGroup.mk' (pCore 2 K) x) ∈
      center Atlas.Codes.HexEvenAutomorphisms) (v : U) :
    ((tripleSixPointCoordinates D a).symm (Multiplicative.ofAdd
      ((Hexacode.centerCharacter
        ⟨a.groupEquiv (QuotientGroup.mk' (pCore 2 K) x),hx⟩ : Hexacode.F) •
          (tripleSixPointCoordinates D a v).toAdd)) : G) =
      (x : G) * (v : G) * (x : G)⁻¹ := by
  have hc := tripleSixPointCoordinates_conjugate D a x v
  have hs := Hexacode.centerCharacter_action Hexacode.evenFieldRepresentation
    (fun w => Hexacode.scalar_eq_omega_smul w)
    ⟨a.groupEquiv (QuotientGroup.mk' (pCore 2 K) x),hx⟩
    (tripleSixPointCoordinates D a v).toAdd
  change Hexacode.evenAction _ _ = _ at hs
  rw [hs] at hc
  exact hc

/-- The actual scalar residual normalizes the original field point and is
transitive on its nonidentity elements, with literal conjugating witnesses. -/
theorem tripleSixScalarResidual_point_transitive (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) :
    tripleSixScalarResidual K ≤ normalizer (tripleSixPoint D a t : Set G) ∧
      ∀ v : G, v ∈ tripleSixPoint D a t → v ≠ 1 →
      ∀ w : G, w ∈ tripleSixPoint D a t → w ≠ 1 →
      ∃ x : G, x ∈ tripleSixScalarResidual K ∧ x * v * x⁻¹ = w := by
  let e := tripleSixPointCoordinates D a
  let P := Submodule.span Hexacode.F {(e t).toAdd}
  let q := a.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hXK : tripleSixScalarResidual K ≤ K := map_subtype_le _
  have him : ((tripleSixScalarResidual K).subgroupOf K).map q =
      center Atlas.Codes.HexEvenAutomorphisms := tripleSixScalarResidual_image D a
  have hn : tripleSixScalarResidual K ≤ normalizer (tripleSixPoint D a t : Set G) := by
    intro x hx
    let xK : K := ⟨x,hXK hx⟩
    have hz : q xK ∈ center Atlas.Codes.HexEvenAutomorphisms :=
      him ▸ mem_map_of_mem q hx
    apply mem_normalizer_fintype
    rintro v ⟨u,hu,rfl⟩
    let r : Hexacode.F := Hexacode.centerCharacter ⟨q xK,hz⟩
    have hc := scalar_conjugate D a xK hz u
    change (xK : G) * (u : G) * (xK : G)⁻¹ ∈ tripleSixPoint D a t
    rw [←hc]
    refine ⟨e.symm (Multiplicative.ofAdd (r • (e u).toAdd)),?_,rfl⟩
    change (e (e.symm (Multiplicative.ofAdd (r • (e u).toAdd)))).toAdd ∈ P
    rw [e.apply_symm_apply]
    exact P.smul_mem r hu
  refine ⟨hn,?_⟩
  rintro v ⟨vU,hv,rfl⟩ hv1 w ⟨wU,hw,rfl⟩ hw1
  change (e vU).toAdd ∈ P at hv
  change (e wU).toAdd ∈ P at hw
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hv
  obtain ⟨s,hs⟩ := Submodule.mem_span_singleton.mp hw
  have hr0 : r ≠ 0 := by
    intro h0
    have hev : e vU = 1 := by
      change (e vU).toAdd = 0
      rw [←hr,h0,zero_smul]
    exact hv1 (congrArg Subtype.val (e.injective (hev.trans e.map_one.symm)))
  have hs0 : s ≠ 0 := by
    intro h0
    have hew : e wU = 1 := by
      change (e wU).toAdd = 0
      rw [←hs,h0,zero_smul]
    exact hw1 (congrArg Subtype.val (e.injective (hew.trans e.map_one.symm)))
  let c : Hexacode.Fˣ := Units.mk0 (s / r) (div_ne_zero hs0 hr0)
  let z := Hexacode.centerCharacter.symm c
  have hzm : z.val ∈ ((tripleSixScalarResidual K).subgroupOf K).map q := by
    rw [him]
    exact z.property
  obtain ⟨x,hx,hxz⟩ := hzm
  have hxscalar : (Hexacode.centerCharacter ⟨q x,him ▸ mem_map_of_mem q hx⟩ : Hexacode.F) =
      s / r := by
    have he : (⟨q x,him ▸ mem_map_of_mem q hx⟩ : center Atlas.Codes.HexEvenAutomorphisms) = z :=
      Subtype.ext hxz
    rw [he,show z = Hexacode.centerCharacter.symm c from rfl,
      Hexacode.centerCharacter.apply_symm_apply]
    rfl
  have hact : (Hexacode.centerCharacter ⟨q x,him ▸ mem_map_of_mem q hx⟩ : Hexacode.F) •
      (e vU).toAdd = (e wU).toAdd := by
    rw [hxscalar,←hr,←hs,smul_smul,div_mul_cancel₀ s hr0]
  have hc := scalar_conjugate D a x (him ▸ mem_map_of_mem q hx) vU
  change (e.symm (Multiplicative.ofAdd
    ((Hexacode.centerCharacter ⟨q x,him ▸ mem_map_of_mem q hx⟩ : Hexacode.F) •
      (e vU).toAdd)) : G) = _ at hc
  rw [hact] at hc
  change (e.symm (e wU) : G) = _ at hc
  rw [e.symm_apply_apply] at hc
  exact ⟨x,hx,hc.symm⟩

/-- The actual point is TI in the original ambient G. The sole ordinary
geometry input is its proved equality with the center of the literal closure. -/
theorem original_tripleSix_held_point_ti (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (hcenter :
      let H := centralizer ({(t : G)} : Set G)
      let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
      centerIn (conjugateSpanBy Lt H) = tripleSixPoint D a t) :
    ChapterI.Section06To08.IsTISubgroup (tripleSixPoint D a t) := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let V := tripleSixPoint D a t
  let N := normalizer (V : Set G)
  obtain ⟨hXN,htrans⟩ := tripleSixScalarResidual_point_transitive D a t
  have htV : (t : G) ∈ V := (tripleSixPoint_properties D a t ht).1
  have ht1 : (t : G) ≠ 1 := fun he => ht (Subtype.ext he)
  have hHN : H ≤ N := by
    change H ≤ normalizer (tripleSixPoint D a t : Set G)
    rw [←hcenter]
    exact normalizes_centerIn (le_normalizer_conjugateSpanBy Lt H)
  apply ChapterI.Section06To08.lemma_I_6_1_1_of_mem_normalizer V
  · intro v hv hv1 g hgv
    obtain ⟨x,hx,hxt⟩ := htrans t htV ht1 v hv hv1
    have hxN : x ∈ N := hXN hx
    have hc : x⁻¹ * g * x ∈ H := by
      apply mem_centralizer_singleton_iff.mpr
      have hg : g * v = v * g := mem_centralizer_singleton_iff.mp hgv
      calc
        (x⁻¹*g*x)*(t : G) = x⁻¹*(g*(x*(t : G)*x⁻¹))*x := by group
        _ = x⁻¹*((x*(t : G)*x⁻¹)*g)*x := by rw [hxt,hg]
        _ = (t : G)*(x⁻¹*g*x) := by group
    have hh := N.mul_mem (N.mul_mem hxN (hHN hc)) (N.inv_mem hxN)
    have he : x * (x⁻¹ * g * x) * x⁻¹ = g := by group
    exact he ▸ hh
  · intro v w hv hw hconj
    by_cases hv1 : v = 1
    · obtain ⟨g,hg⟩ := hconj
      have hw1 : w = 1 := by simpa only [hv1,mul_one,mul_inv_cancel] using hg.symm
      exact ⟨1,by simp only [OneMemClass.coe_one,inv_one,mul_one,hv1,hw1]⟩
    · have hw1 : w ≠ 1 := by
        intro hw1
        obtain ⟨g,hg⟩ := hconj
        apply hv1
        have hh := congrArg (fun z => g⁻¹*z*g) hg
        simpa only [hw1,mul_one,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_inv_cancel_right] using hh
      obtain ⟨x,hx,hxvw⟩ := htrans v hv hv1 w hw hw1
      exact ⟨⟨x,hXN hx⟩,hxvw⟩

end CFSG.Quasithin.Chapter12.Section07
