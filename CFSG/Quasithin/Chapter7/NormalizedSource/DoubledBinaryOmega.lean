module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddCore
public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
import all CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlanes
import all CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddCore

/-!
# The full doubled orbit inside the Sylow omega-center orbit

The paired-plane fixer is S₃. Every two-subgroup lies in an involution
subgroup, and that involution inverts a cubic. In characteristic two,
the involution displacements are fixed by the involution; the cubic norm
then shows that its fixed vectors generate the entire natural–dual pair.
Transporting this calculation through the original component and automizer
puts the full doubled orbit in ⟨Ω₁(Z(T₀))ᴴ⟩. Characteristic two makes this
literal normal closure two-reduced, with quotient H/C_H(⟨Ω₁(Z(T₀))ᴴ⟩).

HasMarking retains the original action as the same plane passes through
component exclusion. NonFFSourceDoubledBinaryOmega applies the containment
and reducedness to the actual minimal escaping group, without identifying
the doubled orbit with its selected seed.
Source: Aschbacher–Smith, proof of Proposition 7.7.3, printed p.707,
refs/quasithin.pdf; B.2.14 supplies reducedness of the omega-center orbit.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open BinaryLinearThree NaturalDual
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOmega
open DoubledBinaryPlanes DoubledBinaryPlaneQuotient DoubledBinaryLocalCore

/-- The original component action and whole automizer marking on a doubled
orbit, retained when the paired plane passes through local overgroups. -/
@[expose] def HasMarking {G : Type*} [_root_.Group G]
    (W₀ L : Subgroup G) [IsElementaryAbelian 2 W₀]
    (E : Additive W₀ ≃ₗ[ZMod 2] Space) : Prop :=
  ∃ hLN : L ≤ normalizer (W₀ : Set G), ∃ q : L →* Group,
    Function.Surjective q ∧ ∃ a : ChapterE.Automizer W₀ ≃* MulAut Group,
      (∀ l w, E (ChapterE.automizerRepresentation W₀
        (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) w) = action (q l) (E w)) ∧
      (∀ l, a (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) = MulAut.conj (q l)) ∧
      ∀ b g w, E (ChapterE.automizerRepresentation W₀ b (E.symm (action g (E w)))) =
        action (a b g) (E (ChapterE.automizerRepresentation W₀ b w))

private theorem cubic_involution_span
    {A X : Type*} [_root_.Group A] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) A X) (s g : A)
    (hs : s ^ 2 = 1) (hg : g ^ 3 = 1) (hsg : s*g = g^2*s)
    (hfix : ∀ x, ρ g x = x → ρ s x = x)
    (N : Submodule (ZMod 2) X)
    (hN : ∀ x, ρ s x = x → x ∈ N)
    (hNg : ∀ x ∈ N, ρ g x ∈ N) : N = ⊤ := by
  have hs2 (x : X) : ρ s (ρ s x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, ← pow_two, hs, map_one, Module.End.one_apply]
  have hg3 (x : X) : ρ g (ρ g (ρ g x)) = x := by
    have hh := congrArg (fun a => ρ a x) hg
    simpa only [pow_succ,pow_zero,mul_one,map_mul,Module.End.mul_apply,map_one,
      Module.End.one_apply] using hh
  have hswap (x : X) : ρ s (ρ g x) = ρ g (ρ g (ρ s x)) := by
    rw [← Module.End.mul_apply, ← map_mul, hsg, map_mul, pow_two, map_mul,
      Module.End.mul_apply, Module.End.mul_apply]
  have hd (x : X) : ρ s x + x ∈ N := by
    apply hN
    rw [map_add,hs2,add_comm]
  apply top_unique
  intro x _
  have he : ρ g x + ρ g (ρ g x) ∈ N := by
    have hh := N.add_mem (hd (ρ g x)) (hNg _ (hNg _ (hd x)))
    rw [hswap,map_add,map_add] at hh
    have hid : ρ g (ρ g (ρ s x)) + ρ g x +
        (ρ g (ρ g (ρ s x)) + ρ g (ρ g x)) = ρ g x + ρ g (ρ g x) := by
      rw [show ρ g (ρ g (ρ s x)) + ρ g x +
          (ρ g (ρ g (ρ s x)) + ρ g (ρ g x)) =
        (ρ g (ρ g (ρ s x)) + ρ g (ρ g (ρ s x))) +
          (ρ g x + ρ g (ρ g x)) by abel, ZModModule.add_self, zero_add]
    exact hid ▸ hh
  have hn : x + ρ g x + ρ g (ρ g x) ∈ N := by
    apply hN
    apply hfix
    rw [map_add,map_add,hg3]
    abel
  have hh := N.sub_mem hn he
  convert hh using 1
  abel

private theorem pair_cubic_involution (v : Vector) (f : Module.Dual (ZMod 2) Vector)
    (hfv : f v = 1) (s g : pairFixer v f) (hs : s ≠ 1)
    (hs2 : s^2 = 1) (hg3 : g^3 = 1) : s*g = g^2*s := by
  let e := pairEquivSymmetric v f hfv
  apply e.injective
  simp only [map_mul,map_pow]
  have hp : ∀ a b : Equiv.Perm (Fin 3), a ≠ 1 → a^2 = 1 → b^3 = 1 →
      a*b = b^2*a := by decide
  exact hp (e s) (e g) (fun hh => hs (e.injective (hh.trans e.map_one.symm)))
    (by rw [← map_pow,hs2,map_one]) (by rw [← map_pow,hg3,map_one])

open ChapterE

/-- The fixed vectors of a two-subgroup in the paired-plane fixer generate
the entire original doubled orbit under its component centralizer. -/
theorem pairedPlane_fixed_generates
    {G : Type*} [_root_.Group G] [Finite G]
    (W₀ L S X : Subgroup G) [IsElementaryAbelian 2 W₀]
    (hLN : L ≤ normalizer (W₀ : Set G))
    (q : L →* Group) (hq : Function.Surjective q)
    (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (hE : ∀ l w, E (automizerRepresentation W₀
      (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) w) = action (q l) (E w))
    (a : Automizer W₀ ≃* MulAut Group)
    (ha : ∀ l, a (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) = MulAut.conj (q l))
    (hcov : ∀ b g w, E (automizerRepresentation W₀ b (E.symm (action g (E w)))) =
      action (a b g) (E (automizerRepresentation W₀ b w)))
    (v : Vector) (f : Module.Dual (ZMod 2) Vector) (hfv : f v = 1)
    (hpS : IsPGroup 2 S) (hSN : S ≤ normalizer (W₀ : Set G))
    (hSC : S ≤ centralizer (ambientPlane W₀ E v f : Set G))
    (hXN : L ⊓ centralizer (ambientPlane W₀ E v f : Set G) ≤ normalizer (X : Set G))
    (hfixX : W₀ ⊓ centralizer (S : Set G) ≤ X) : W₀ ≤ X := by
  classical
  let n : S →* Automizer W₀ := W₀.normalizerMonoidHom.rangeRestrict.comp (inclusion hSN)
  have hinner (s : S) : a (n s) ∈ MulAut.innerSubgroup Group :=
    doubledBinary_ambientPlane_fixer_inner W₀ E a hcov (inclusion hSN s) v f hfv
      (hSC s.property)
  let c : Group ≃* MulAut.innerSubgroup Group :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot)
  let j₀ : S →* Group := c.symm.toMonoidHom.comp
    ((a.toMonoidHom.comp n).codRestrict _ hinner)
  have hj₀ (s : S) : MulAut.conj (j₀ s) = a (n s) :=
    congrArg Subtype.val (c.apply_symm_apply _)
  have hact (s : S) (w : Additive W₀) :
      E (automizerRepresentation W₀ (n s) w) = action (j₀ s) (E w) := by
    obtain ⟨l,hl⟩ := hq (j₀ s)
    have he : W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l) = n s :=
      a.injective (by rw [ha,hl,hj₀])
    rw [← he,hE,hl]
  have hjp (s : S) : j₀ s ∈ pairFixer v f := by
    have hfixed (x : Space) (hx : ((E.symm x).toMul : G) ∈ ambientPlane W₀ E v f) :
        action (j₀ s) x = x := by
      have he : automizerRepresentation W₀ (n s) (E.symm x) = E.symm x := by
        apply Additive.toMul.injective
        apply Subtype.ext
        change (s : G) * ((E.symm x).toMul : G) * (s : G)⁻¹ = ((E.symm x).toMul : G)
        rw [← hSC s.property _ hx,mul_inv_cancel_right]
      have hh := hact s (E.symm x)
      rw [he,E.apply_symm_apply] at hh
      exact hh.symm
    have haxes := (ambientPlane_le_iff W₀ E v f _).mp le_rfl
    exact ⟨congrArg Prod.fst (hfixed (v,0) haxes.1),
      congrArg Prod.snd (hfixed (0,f) haxes.2)⟩
  let j : S →* pairFixer v f := j₀.codRestrict _ hjp
  obtain ⟨P,hP⟩ := (hpS.of_surjective j.rangeRestrict j.rangeRestrict_surjective).exists_le_sylow
  have hcard : Nat.card P = 2 := by
    rw [P.card_eq_multiplicity,Nat.card_congr (pairEquivSymmetric v f hfv).toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
    rw [show 6 = 2*3 from rfl, Nat.factorization_mul (by decide) (by decide)]
    norm_num
  obtain ⟨s,hs,hunique⟩ := (Nat.card_eq_two_iff' (1 : P)).mp hcard
  have hs' : (s : pairFixer v f) ≠ 1 := fun hh => hs (Subtype.ext hh)
  have hs2 : (s : pairFixer v f)^2 = 1 := congrArg Subtype.val
    (hcard ▸ pow_card_eq_one' (x := s))
  have hmem (b : S) : j b = 1 ∨ j b = s := by
    let z : P := ⟨j b,hP ⟨b,rfl⟩⟩
    by_cases hz : z = 1
    · exact Or.inl (congrArg Subtype.val hz)
    · exact Or.inr (congrArg Subtype.val (hunique z hz))
  obtain ⟨g,hg,hgv,hgf,hgfix⟩ := DoubledBinaryOddCore.pairedPlane_cubic v f hfv
  let gP : pairFixer v f := ⟨g,hgv,hgf⟩
  let N := coordinateSubspace W₀ E X
  have hNg : ∀ x ∈ N, action g x ∈ N := by
    obtain ⟨l,hl⟩ := hq g
    have hlC : (l : G) ∈ centralizer (ambientPlane W₀ E v f : Set G) :=
      (DoubledBinaryOddCore.component_plane_fixer W₀ L hLN q E hE v f l).mpr
        (hl.symm ▸ show g ∈ pairFixer v f from ⟨hgv,hgf⟩)
    intro x hx
    have hc (z : Space) : z ∈ N ↔ ((E.symm z).toMul : G) ∈ X := by
      simpa only [E.apply_symm_apply] using coordinate_mem W₀ E X (E.symm z)
    rw [hc] at hx ⊢
    change DoubledBinaryOddCore.coordinates W₀ E (action g x) ∈ X
    rw [← hl,DoubledBinaryOddCore.coordinates_conj W₀ L hLN q E hE]
    exact (mem_normalizer_iff.mp (hXN ⟨l.property,hlC⟩) _).mp hx
  have hNs : ∀ x, action (s : pairFixer v f) x = x → x ∈ N := by
    intro x hx
    have hc : x ∈ N ↔ ((E.symm x).toMul : G) ∈ X := by
      simpa only [E.apply_symm_apply] using coordinate_mem W₀ E X (E.symm x)
    apply hc.mpr
    apply hfixX
    refine ⟨(E.symm x).toMul.property,?_⟩
    intro b hb
    have he : action (j₀ ⟨b,hb⟩) x = x := by
      rcases hmem ⟨b,hb⟩ with he | he
      · have hh : j₀ ⟨b,hb⟩ = 1 := congrArg Subtype.val he
        rw [hh,map_one,Module.End.one_apply]
      · have hh : j₀ ⟨b,hb⟩ = (s : pairFixer v f) := congrArg Subtype.val he
        rwa [hh]
    have hh := hact ⟨b,hb⟩ (E.symm x)
    rw [E.apply_symm_apply,he] at hh
    have hz : automizerRepresentation W₀ (n ⟨b,hb⟩) (E.symm x) = E.symm x :=
      E.injective (hh.trans (E.apply_symm_apply x).symm)
    have hv := congrArg (fun w : Additive W₀ => (w.toMul : G)) hz
    change b * ((E.symm x).toMul : G) * b⁻¹ = ((E.symm x).toMul : G) at hv
    exact mul_inv_eq_iff_eq_mul.mp hv
  have hNtop : N = ⊤ := by
    apply cubic_involution_span (action.comp (pairFixer v f).subtype) s gP hs2
      (Subtype.ext hg) (pair_cubic_involution v f hfv s gP hs' hs2 (Subtype.ext hg))
      ?_ N hNs hNg
    intro x hx
    have hp := hgfix x hx
    have hfixed : pairedPlane v f ≤ fixedSpace action (zpowers (s : Group)) := by
      rw [pairedPlane_le_iff]
      exact ⟨(mem_fixedSpace_zpowers_iff _ _ _).mpr
        (Prod.ext s.val.property.1 (map_zero (W.dual (s : Group)))),
        (mem_fixedSpace_zpowers_iff _ _ _).mpr
        (Prod.ext (map_zero (W (s : Group))) s.val.property.2)⟩
    exact (mem_fixedSpace_zpowers_iff action (s : Group) x).mp (hfixed hp)
  intro w hw
  apply (coordinate_mem W₀ E X (Additive.ofMul ⟨w,hw⟩)).mp
  change E _ ∈ N
  rw [hNtop]
  trivial

open Stellmacher Theory.GroupTheory

/-- Containment of the full doubled orbit in the actual Sylow omega-center
orbit of an overgroup containing its component plane-centralizer. -/
theorem orbit_le_omegaClosure
    {G : Type*} [_root_.Group G] [Finite G]
    (W₀ L S H : Subgroup G) [IsElementaryAbelian 2 W₀]
    (E : Additive W₀ ≃ₗ[ZMod 2] Space) (hmark : HasMarking W₀ L E)
    (v : Vector) (f : Module.Dual (ZMod 2) Vector) (hfv : f v = 1)
    (hWS : W₀ ≤ S) (hpS : IsPGroup 2 S) (hSN : S ≤ normalizer (W₀ : Set G))
    (hSC : S ≤ centralizer (ambientPlane W₀ E v f : Set G))
    (hLH : L ⊓ centralizer (ambientPlane W₀ E v f : Set G) ≤ H) :
    W₀ ≤ conjugateSpanBy (omegaOneCenterAmbient S) H := by
  obtain ⟨hLN,q,hq,a,hE,ha,hcov⟩ := hmark
  apply pairedPlane_fixed_generates W₀ L S _ hLN q hq E hE a ha hcov v f hfv hpS hSN hSC
    (hLH.trans (le_normalizer_conjugateSpanBy _ _))
  intro w hw
  apply le_conjugateSpanBy
  exact (mem_omegaOneCenterAmbient_iff S w).mpr
    ⟨hWS hw.1,elemPow_eq_one_of_isElementaryAbelian w hw.1,hw.2⟩

/-- The same ambient omega-center orbit is reduced inside its actual
characteristic-two overgroup, with its literal centralizer quotient. -/
theorem omegaClosure_reduced
    {G : Type*} [_root_.Group G] [Finite G]
    (H S : Subgroup G) (P : Sylow 2 H)
    (hP : (P : Subgroup H).map H.subtype = S)
    (hchar : centralizer (pCore 2 H : Set H) ≤ pCore 2 H) :
    IsPReduced 2 ((conjugateSpanBy (omegaOneCenterAmbient S) H).subgroupOf H) := by
  have hz : omegaOneCenterAmbient S = (omegaOneCenterAmbient (P : Subgroup H)).map H.subtype := by
    rw [← hP,omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective]
  have hzH : omegaOneCenterAmbient S ≤ H := hz.trans_le (map_subtype_le _)
  have hh := omegaCenter_normalClosure_reduced P hchar
  rw [← normalClosure_subgroupOf_eq_conjugateSpanBy _ _ hzH,hz]
  change IsPReduced 2 (normalClosure
    (((omegaOneCenterAmbient (P : Subgroup H)).map H.subtype).comap H.subtype : Set H))
  rw [comap_map_eq_self_of_injective H.subtype_injective]
  exact hh

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOmega
