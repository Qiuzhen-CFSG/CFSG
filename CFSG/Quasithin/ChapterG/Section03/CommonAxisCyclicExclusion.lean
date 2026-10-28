module

public import CFSG.Quasithin.ChapterG.Section03.SQTKRootSpanOneBlock
public import CFSG.Quasithin.ChapterG.Section03.CommonCenterSource
public import Theory.Representation.BinaryTransvectionGroups.RootFourSylowFixed
public import Theory.Representation.BinaryCyclicPointDualSpan

/-!
# A fully moved common-axis four-group excludes a cyclic fixed point

The contragredient action turns the actual common-axis four-group into a
common-center subgroup. The SQTK source and cubic residual force a full
linear action on its literal root span. Evaluation at the original cyclic
point would give a covector fixed by the residual and a full Sylow, which
the moved root four-group excludes. The resulting annihilation of the root
span contradicts cyclicity of the unchanged original point.

Source: Aschbacher--Smith 12.7.18, printed p.845. Neither a spanning dual
orbit nor an invariant complement is assumed.
-/

public noncomputable section
open Subgroup BinaryLinear BinaryTransvectionGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section03

universe u
variable {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {X : Type u} [Group X] [Finite X]

omit [Finite V] in
private theorem hypotheses_of_large_root
    {Q : Subgroup (BinaryLinear.GL V)} [Finite Q] (hcore : pCore 2 Q = ⊥)
    (x : V) (hx : x ≠ 0) (hc : 2 < Nat.card (rootGroup Q x)) :
    Hypotheses Q (MulAction.orbit Q x) := by
  refine ⟨?_, ⟨x, rfl⟩, ?_⟩
  · rintro y ⟨g, rfl⟩
    exact fun he => hx (g.val.injective (he.trans (g.val.map_zero).symm))
  · intro y hy
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hy
    change 1 < Group.rank (rootQuotientImage Q (g.val x))
    have hc' : 2 < Nat.card (rootGroup Q (g.val x)) := by
      rw [← rootGroup_conjugate g.property x]
      exact hc.trans_eq
        (Nat.card_congr ((MulAut.conj g.val).subgroupMap (rootGroup Q x)).toEquiv)
    let q := QuotientGroup.mk' (pCore 2 Q)
    have hi : Function.Injective q := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [QuotientGroup.ker_mk', hcore]
    have hcard : Nat.card (rootQuotientImage Q (g.val x)) =
        Nat.card (rootGroup Q (g.val x)) :=
      (Nat.card_congr (((rootGroup Q (g.val x)).subgroupOf Q).equivMapOfInjective q hi).toEquiv).symm.trans
        (Nat.card_congr (subgroupOfEquivOfLe (rootGroup_le Q (g.val x))).toEquiv)
    let : IsElementaryAbelian 2 (rootQuotientImage Q (g.val x)) :=
      rootQuotientImage_elementaryAbelian Q (g.val x)
    have hb : Nat.card (rootQuotientImage Q (g.val x)) ≤
        2 ^ Group.rank (rootQuotientImage Q (g.val x)) :=
      Nat.le_of_dvd (by positivity) (card_dvd_exponent_pow_rank' _
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 _)))
    by_contra hn
    have hp := pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) (not_lt.mp hn)
    rw [hcard] at hb
    omega

/-- The actual common-axis four-group, cubic residual, and original Sylow
cannot coexist with a cyclic point fixed by the residual and Sylow. -/
theorem common_axis_cyclic_exclusion
    (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (Q : Subgroup (BinaryLinear.GL V)) (q : X →* Q) (hq : Function.Surjective q)
    (hcore : pCore 2 Q = ⊥) (f : DualSpace V) (hf : f ≠ 0)
    (A J : Subgroup Q) (hA : A.map Q.subtype ≤ axisRootGroup Q f)
    (hcard : Nat.card A = 4) (hmove : A = ⁅A, J⁆)
    (hJ : IsPPerfect 2 J) (hc : Nat.card (J ⧸ pCore 2 J) = 3)
    (S : Sylow 2 Q)
    (hSA : (S : Subgroup Q) ≤ normalizer (A : Set Q))
    (hJA : J ≤ normalizer (A : Set Q))
    (hSJ : (S : Subgroup Q) ≤ normalizer (J : Set Q))
    (x : V)
    (hspan : Submodule.span (ZMod 2) (Set.range (fun g : Q => g.val x)) = ⊤)
    (hJx : ∀ j ∈ J, j.val x = x) (hSx : ∀ s ∈ S, s.val x = x) : False := by
  classical
  let : Finite (DualSpace V) := Finite.of_injective
    (fun l : DualSpace V => (l : V → ZMod 2)) DFunLike.coe_injective
  let D := dualGroup Q
  let e : Q ≃* D := dualGroupEquiv Q
  let AD := A.map e.toMonoidHom
  let JD := J.map e.toMonoidHom
  let SD : Sylow 2 D := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hcoreD : pCore 2 D = ⊥ := dualGroup_twoCore_eq_bot hcore
  have hAD : AD.map D.subtype ≤ rootGroup D f := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨a, ha, rfl⟩ := hg
    exact (contragredient_mem_axisRoot_iff Q f a.val).mpr (hA (mem_map_of_mem Q.subtype ha))
  have hcardD : Nat.card AD = 4 := by
    rw [show AD = A.map e.toMonoidHom from rfl, card_map_of_injective e.injective, hcard]
  have hcardRoot : 2 < Nat.card (rootGroup D f) := by
    have hb := card_le_of_le hAD
    rw [card_map_of_injective D.subtype_injective, hcardD] at hb
    omega
  have hsource := hypotheses_of_large_root hcoreD f hf hcardRoot
  obtain ⟨hfull, hdec, hlocal⟩ := source_conclusions_of_twoCore_eq_bot hsource hcoreD
  have hmoveD : AD = ⁅AD, JD⁆ := by
    change A.map e.toMonoidHom = ⁅A.map e.toMonoidHom, J.map e.toMonoidHom⁆
    rw [← map_commutator, ← hmove]
  let eJ : J ≃* JD := J.equivMapOfInjective e.toMonoidHom e.injective
  have hJD : IsPPerfect 2 JD := hJ.of_surjective eJ.toMonoidHom eJ.surjective
  have hcD : Nat.card (JD ⧸ pCore 2 JD) = 3 := by
    let E := QuotientGroup.congr (pCore 2 J) (pCore 2 JD) eJ (pCore_map_iso 2 eJ)
    exact (Nat.card_congr E.toEquiv).symm.trans hc
  have hSJD : (SD : Subgroup D) ≤ normalizer (JD : Set D) :=
    (map_mono hSJ).trans (le_normalizer_map e.toMonoidHom)
  have hADne : AD ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hcardD
    omega
  obtain ⟨hpar, hker, hgeninj, hAinj, hone, honto, hcardB, hdim, hroot, hmoveB, hJB, hcB⟩ :=
    sqtk_root_span_one_block hX D (e.toMonoidHom.comp q) (e.surjective.comp hq)
      f hsource hcoreD hfull hdec hlocal AD JD hAD hADne hmoveD hJD hcD SD hSJD
  let B := Submodule.span (ZMod 2) (MulAction.orbit D f)
  let ρ : D →* BinaryLinear.GL B := action D B hpar
  let AB := AD.map ρ
  let JB := JD.map ρ
  let SB : Sylow 2 (BinaryLinear.GL B) := SD.mapSurjective (f := ρ) (MonoidHom.range_eq_top.mp honto)
  have hcardAB : Nat.card AB = 4 := hcardB.trans hcardD
  let : Nontrivial AB := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcardAB]; decide)
  let : IsElementaryAbelian 2 AB := elementaryAbelian_of_le_radical
    AB.subtype AB.subtype_injective _ (fun g => hroot g.property)
  let : IsKleinFour AB := ⟨hcardAB, IsElementaryAbelian.exponent_eq_prime⟩
  have hJAD : JD ≤ normalizer (AD : Set D) :=
    (map_mono hJA).trans (le_normalizer_map e.toMonoidHom)
  have hSAD : (SD : Subgroup D) ≤ normalizer (AD : Set D) :=
    (map_mono hSA).trans (le_normalizer_map e.toMonoidHom)
  have hJAB : JB ≤ normalizer (AB : Set (BinaryLinear.GL B)) :=
    (map_mono hJAD).trans (le_normalizer_map ρ)
  have hSAB : (SB : Subgroup (BinaryLinear.GL B)) ≤ normalizer (AB : Set (BinaryLinear.GL B)) :=
    (map_mono hSAD).trans (le_normalizer_map ρ)
  let fB : B := ⟨f, Submodule.subset_span (MulAction.mem_orbit_self f)⟩
  have hfB : fB ≠ 0 := fun he => hf (congrArg Subtype.val he)
  have hzero := dual_fixedSpace_sup_sylow_eq_bot_of_root_four fB hfB AB JB hroot hJB hJAB hmoveB SB hSAB
  let ℓ : DualSpace B := (Module.Dual.eval (ZMod 2) V x).comp B.subtype
  have heval (g : Q) (hg : g.val x = x) : contragredient (ρ (e g)) ℓ = ℓ := by
    ext w
    change ℓ ((ρ (e g))⁻¹ w) = ℓ w
    rw [show (ρ (e g))⁻¹ = ρ (e g⁻¹) by simp]
    change (w : DualSpace V) (g.val x) = (w : DualSpace V) x
    rw [hg]
  have hfix : ℓ ∈ fixedSpace (dualGroup (JB ⊔ (SB : Subgroup (BinaryLinear.GL B)))) := by
    have hle : JB ⊔ (SB : Subgroup (BinaryLinear.GL B)) ≤
        (MulAction.stabilizer (BinaryLinear.GL (DualSpace B)) ℓ).comap contragredient := by
      apply sup_le
      · rintro _ ⟨j, hj, rfl⟩
        obtain ⟨g, hg, rfl⟩ := hj
        exact heval g (hJx g hg)
      · rintro _ ⟨s, hs, rfl⟩
        obtain ⟨g, hg, rfl⟩ := hs
        exact heval g (hSx g hg)
    rintro _ ⟨g, hg, rfl⟩
    exact hle hg
  have hℓ : ℓ = 0 := by simpa only [hzero, Submodule.mem_bot] using hfix
  have hBzero : B = ⊥ := Representation.dual_subspace_eq_bot_of_cyclic_point_annihilation
    Q x hspan B hpar (fun l hl => congrArg (fun F : DualSpace B => F ⟨l, hl⟩) hℓ)
  have hfmem : f ∈ B := Submodule.subset_span (MulAction.mem_orbit_self f)
  rw [hBzero, Submodule.mem_bot] at hfmem
  exact hf hfmem

end CFSG.Quasithin.ChapterG.Section03
