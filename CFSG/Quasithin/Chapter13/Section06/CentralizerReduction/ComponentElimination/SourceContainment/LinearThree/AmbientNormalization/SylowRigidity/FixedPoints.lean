module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Natural
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.CenterFrattiniSource.OmegaActions.Nilpotent
public import Theory.GroupTheory.CyclicNormalCentralizer
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement

/-!
# Sylow fixed points in the A.3.6 Fitting subgroup

For a perfect group in either exceptional A.3.6 alternative, each Sylow
two-subgroup has no nonidentity fixed points on the actual omega–Frattini
quotient of any prime core in the Fitting subgroup. Irreducibility and the
quaternion subgroup in the action image prove this directly.

In an abelian core, a nonidentity fixed point has a nonidentity order-p
power in omega, whose Frattini subgroup is trivial. In an extraspecial core,
omega is the whole core, and the Frattini subgroup lies in its cyclic center.
A perfect group centralizes every cyclic normal subgroup. These prime-core
bounds combine by taking the Sylow subgroups of the fixed-point subgroup
inside the nilpotent Fitting subgroup. The quasisimple alternatives follow
from centrality of their solvable radical.

The final application uses the literal image of a C-component D in A/O₂(A),
proving both the ambient two-core condition and C-component membership. It
supplies exactly the fixed-point premise of the parent Sylow-rigidity
assembly, without importing that parent and creating a cycle. No SQTK,
center–Frattini equality, or exponent-p assumption on a homocyclic core is
used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.6 and
its proof, printed pp.43–45; application to 13.6.20, printed p.931.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.RadicalActions
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.AmbientNormalization.SylowRigidity.FixedPoints

private theorem fixed_eq_one {A V : Type*} [Group A] [Group V]
    (ρ : A →* MulAut V)
    (hi : ∀ U : Subgroup V, (∀ a x, x ∈ U → ρ a x ∈ U) → U = ⊥ ∨ U = ⊤)
    (hn : ∃ f : QuaternionGroup 2 →* ρ.range, Function.Injective f)
    (x : V) (hx : ∀ a, ρ a x = x) : x = 1 := by
  let U : Subgroup V := ⨅ a, (ρ a).fixedSubgroup
  have hmem : x ∈ U := by simpa [U] using hx
  have hinv : ∀ a y, y ∈ U → ρ a y ∈ U := by
    intro a y hy
    have hy' : ∀ b, ρ b y = y := by simpa [U] using hy
    rw [hy' a]
    exact hy
  rcases hi U hinv with hb | ht
  · simpa [hb] using hmem
  · have hall (a : A) (y : V) : ρ a y = y := by
      have hy : y ∈ U := ht ▸ mem_top y
      simpa [U] using (show ∀ b, ρ b y = y from by simpa [U] using hy) a
    have hr : ∀ z : ρ.range, z = 1 := by
      rintro ⟨z, a, rfl⟩
      apply Subtype.ext
      exact MulEquiv.ext (hall a)
    obtain ⟨f, hf⟩ := hn
    have hh := hf ((hr (f (QuaternionGroup.xa 0))).trans (hr (f 1)).symm)
    cases hh

variable {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
variable {p : ℕ} [Fact p.Prime]

private theorem omega_fixed_mem_frattini
    (h : A36Natural K ∨ A36Nilpotent K)
    (hd : p ∣ Nat.card (fittingSubgroup K)) (S : Sylow 2 K)
    (x : omegaCore p K) (hx : (x : K) ∈ centralizer (S : Set K)) :
    x ∈ frattini (omegaCore p K) := by
  have ho : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by
    have := (RadicalStructure.radical_core h hd).2.1
    omega)
  have ha := h.elim (fun hn => natural_sylow_actions hn hd S)
    (fun hn => CenterFrattiniSource.nilpotent_sylow_actions hn ho hd S)
  apply (QuotientGroup.eq_one_iff x).mp
  apply fixed_eq_one ((omegaFrattiniAction p K).comp (S : Subgroup K).subtype) ha.1 ha.2
  intro s
  change quotientAut (frattini (omegaCore p K)) (omegaCoreAction p K s)
    (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ x
  rw [quotientAut_apply_mk]
  apply congrArg (QuotientGroup.mk' _)
  apply Subtype.ext
  rw [omegaCoreAction_apply, mem_centralizer_iff.mp hx s s.property,
    mul_inv_cancel_right]

private theorem abelian_fixed_eq_one
    (h : A36Natural K ∨ A36Nilpotent K)
    (hd : p ∣ Nat.card (fittingSubgroup K)) (S : Sylow 2 K)
    [IsMulCommutative (pCore p K)]
    (x : pCore p K) (hx : (x : K) ∈ centralizer (S : Set K)) : x = 1 := by
  let : IsElementaryAbelian p (omega (pCore p K) (p := p) 1) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative (pCore p K)
  let : IsElementaryAbelian p (omegaCore p K) :=
    IsElementaryAbelian.map_subtype
  let : Fact (IsPGroup p (omegaCore p K)) := ⟨Nilpotent.omega_isPGroup⟩
  have hphi : frattini (omegaCore p K) = ⊥ :=
    frattini_eq_bot_of_isElementaryAbelian (p := p)
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := p) (G := K)).exists_orderOf_eq_pow x
  by_contra hne
  have hn0 : n ≠ 0 := by
    intro he
    simp only [he, pow_zero, orderOf_eq_one_iff] at hn
    exact hne hn
  let y : pCore p K := x ^ (p ^ (n - 1))
  have hyp : y ^ p = 1 := by
    dsimp [y]
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n), ← hn,
      pow_orderOf_eq_one]
  have hyn : y ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    rw [hn]
    exact pow_lt_pow_right₀ (Fact.out : p.Prime).one_lt (by omega)
  have hyw : (y : K) ∈ omegaCore p K :=
    ⟨y, subset_closure (by simpa only [Set.mem_ofPred_eq, pow_one] using hyp), rfl⟩
  have hyc : (y : K) ∈ centralizer (S : Set K) := (centralizer (S : Set K)).pow_mem hx _
  have hyphi := omega_fixed_mem_frattini h hd S ⟨y, hyw⟩ hyc
  rw [hphi, mem_bot] at hyphi
  exact hyn (Subtype.ext (congrArg (fun z : omegaCore p K => (z : K)) hyphi))

private theorem extraspecial_fixed_central
    (h : A36Natural K ∨ A36Nilpotent K)
    (hd : p ∣ Nat.card (fittingSubgroup K)) (S : Sylow 2 K)
    (he : LocalModels.OddExtraspecialThree p (pCore p K))
    (x : pCore p K) (hx : (x : K) ∈ centralizer (S : Set K)) :
    (x : K) ∈ center K := by
  let : IsExtraspecial p (pCore p K) := he.1.1
  have hW : omegaCore p K = pCore p K := by
    unfold omegaCore
    rw [RadicalStructure.omega_top he.2, ← MonoidHom.range_eq_map, range_subtype]
  let e := MulEquiv.subgroupCongr hW
  have hxphi : x ∈ frattini (pCore p K) :=
    frattini_le_comap_frattini_of_surjective (φ := e.toMonoidHom) e.surjective
      (omega_fixed_mem_frattini h hd S (e.symm x) hx)
  let : IsElementaryAbelian p (pCore p K ⧸ center (pCore p K)) :=
    IsExtraspecial.quotient_elementary_abelian p (pCore p K)
  let : Fact (IsPGroup p (pCore p K ⧸ center (pCore p K))) :=
    ⟨IsElementaryAbelian.isPGroup p _⟩
  have hphi : frattini (pCore p K) ≤ center (pCore p K) := by
    have hle := frattini_le_comap_frattini_of_surjective
      (QuotientGroup.mk'_surjective (center (pCore p K)))
    rw [frattini_eq_bot_of_isElementaryAbelian
      (R := pCore p K ⧸ center (pCore p K)) (p := p)] at hle
    simpa using hle
  let Z := (center (pCore p K)).map (pCore p K).subtype
  let : Z.Characteristic := characteristic_of_characteristic_of_characteristic
  let : IsCyclic (center (pCore p K)) :=
    isCyclic_of_prime_card (IsExtraspecial.center_order_p p (pCore p K))
  let : IsCyclic Z := isCyclic_of_surjective _
    ((pCore p K).subtype.subgroupMap_surjective (center (pCore p K)))
  have hcent := commutator_le_centralizer_of_isCyclic_normal Z
  rw [Group.IsPerfect.commutator_eq_top] at hcent
  have hxZ : (x : K) ∈ Z := ⟨x, hphi hxphi, rfl⟩
  apply mem_center_iff.mpr
  intro g
  exact (mem_centralizer_iff.mp (hcent (mem_top g)) x hxZ).symm

/-- Every prime-core fixed point is central, retaining all homocyclic exponents. -/
theorem core_fixed_central
    (h : A36Natural K ∨ A36Nilpotent K)
    (hd : p ∣ Nat.card (fittingSubgroup K)) (S : Sylow 2 K) :
    pCore p K ⊓ centralizer (S : Set K) ≤ center K := by
  intro x hx
  rcases (RadicalStructure.radical_core h hd).2.2 with he | he | he
  · let := he.1.toIsMulCommutative
    have hx1 := abelian_fixed_eq_one h hd S ⟨x, hx.1⟩ hx.2
    have hxv : x = 1 := congrArg Subtype.val hx1
    exact hxv ▸ (center K).one_mem
  · exact extraspecial_fixed_central h hd S he ⟨x, hx.1⟩ hx.2
  · obtain ⟨a, _, ⟨e⟩⟩ := he
    let : IsMulCommutative (pCore p K) :=
      IsMulCommutative.of_comm (fun x y => e.injective (by simp only [map_mul, mul_comm]))
    have hx1 := abelian_fixed_eq_one h hd S ⟨x, hx.1⟩ hx.2
    have hxv : x = 1 := congrArg Subtype.val hx1
    exact hxv ▸ (center K).one_mem

omit [Fact p.Prime] in
/-- Assemble the prime-core containments inside the nilpotent Fitting subgroup. -/
theorem exceptional_fixed_central
    (h : A36Natural K ∨ A36Nilpotent K) (S : Sylow 2 K) :
    fittingSubgroup K ⊓ centralizer (S : Set K) ≤ center K := by
  let H := fittingSubgroup K ⊓ centralizer (S : Set K)
  have hHF : H ≤ fittingSubgroup K := inf_le_left
  have hHC : H ≤ centralizer (S : Set K) := inf_le_right
  change H ≤ center K
  rw [← Sylow.iSup_sylow_map_eq_top (N := H), Subgroup.map_iSup]
  refine iSup_le fun p => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hp => ?_
  let : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  let P := (default : Sylow p H)
  let i := inclusion hHF
  obtain ⟨Q, hQ⟩ := (P.isPGroup'.map i).exists_le_sylow
  have hm : (P : Subgroup H).map H.subtype ≤ pCore p K := by
    have he : H.subtype = (fittingSubgroup K).subtype.comp i := rfl
    rw [he, ← map_map]
    exact (map_mono hQ).trans (Q.map_le_pCore inferInstance inferInstance p)
  have hd : p ∣ Nat.card (fittingSubgroup K) :=
    (Nat.dvd_of_mem_primeFactors hp).trans (card_dvd_of_le hHF)
  apply le_trans (le_inf hm ?_) (core_fixed_central h hd S)
  exact (map_le_range _ _).trans (by simpa using hHC)

omit [Group.IsPerfect K] [Fact p.Prime] in
/-- Sylow fixed points in the Fitting subgroup of a literal A.3.6 C-component. -/
theorem fitting_fixed_central {X : Type*} [Group X] [Finite X]
    (_hX : pCore 2 X = ⊥) {C : Subgroup X} (hC : C.IsCComponent)
    (ha : A36Conclusion C) (S : Sylow 2 C) :
    fittingSubgroup C ⊓ centralizer (S : Set C) ≤ center C := by
  let : Group.IsPerfect C := hC.perfect
  by_cases hq : IsQuasisimple C
  · let := hq
    exact inf_le_left.trans ((le_solvableRadical _ inferInstance inferInstance).trans
      IsQuasisimple.solvableRadical_le_center)
  · exact exceptional_fixed_central (RadicalStructure.nonsimple_radical ha hq) S

/-- The exact fixed-point premise on the image of D in A/O₂(A). -/
theorem quotient_image_fixed_central {A : Type*} [Group A] [Finite A]
    (D : Subgroup A) (hD : D.IsCComponent)
    (ha : A36Conclusion (D.map (QuotientGroup.mk' (pCore 2 A))))
    (S : Sylow 2 (D.map (QuotientGroup.mk' (pCore 2 A)))) :
    fittingSubgroup (D.map (QuotientGroup.mk' (pCore 2 A))) ⊓
      centralizer (S : Set (D.map (QuotientGroup.mk' (pCore 2 A)))) ≤
        center (D.map (QuotientGroup.mk' (pCore 2 A))) := by
  let := pCore_isNilpotent (p := 2) (G := A)
  exact fitting_fixed_central (pCore_quotient_pCore_eq_bot 2) (hD.map_quotient _) ha S

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.AmbientNormalization.SylowRigidity.FixedPoints
