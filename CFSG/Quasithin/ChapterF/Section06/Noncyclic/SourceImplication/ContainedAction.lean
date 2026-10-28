module
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.LocalCubic
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.TernaryObstruction
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.SupercriticalAction

/-!
# The contained-local-residual case of F.6.16

The universal F.6.13 input retains all four source conclusions, including
the actual Sylow subgroup and both relative-normality conditions.
If one local residual lies in the normal three-subgroup X, F.6.13 makes
the other local two-core elementary abelian. Its two-residual has intrinsic
cubic quotient, so the concrete GL₂(3) result kills that intrinsic two-core.
Coprime torsion places it in O³ of the actual action kernel. It therefore
centralizes X, and the relative normality clause of F.6.13 kills it.
Both local residuals now generate a three-group.

The last theorem applies this calculation to the actual supercritical
Frattini representation. In the contrary branch neither local residual
can lie in the embedded supercritical subgroup. The full earlier F.6.13
input remains with qt-f06-rigidity and the final source assembly owner.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
F.6.13 and F.6.16, printed pp.307–309 (1 March 2004 manuscript).
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Noncyclic
universe u

/-- The full earlier source F.6.13, including relative normality and both
normality-implies-triviality clauses. The core of the local residual is
embedded by its two literal subtype maps. -/
@[expose] def GoldschmidtRigidityInput : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (G₁ G₂ : Subgroup G),
    IsGoldschmidtTriple G₁ G₂ → pCore 2 G = ⊥ →
    ∀ (X : Subgroup G) (_ : X.Normal),
      (pResidual 2 G₁).map G₁.subtype ≤ X →
      ¬ (pResidual 2 G₂).map G₂.subtype ≤ X →
      let Q₁ := (pCore 2 G₁).map G₁.subtype
      let Q₂ := (pCore 2 G₂).map G₂.subtype
      let L₁ := (pResidual 2 G₁).map G₁.subtype
      let R₂ := pResidual 2 G₂
      let K₂ := (pCore 2 R₂).map (G₂.subtype.comp R₂.subtype)
      (X ⊔ G₂ = ⊤) ∧ (X ⊔ Q₂ : Subgroup G).Normal ∧
      (∃ S : Sylow 2 (X ⊔ Q₂ : Subgroup G),
        (S : Subgroup (X ⊔ Q₂ : Subgroup G)).map (X ⊔ Q₂ : Subgroup G).subtype = Q₂) ∧
      Nonempty (L₁ ≃* Multiplicative (ZMod 3)) ∧
      IsElementaryAbelian 2 Q₂ ∧ primeRank 2 Q₂ ≤ 3 ∧
      ((Q₂.subgroupOf (Q₂ ⊔ L₁)).Normal → Q₂ = ⊥) ∧
      ((K₂.subgroupOf (Q₂ ⊔ L₁)).Normal → K₂ = ⊥) ∧
      (pPrimeCore 2 X = ⊤ → ⁅Q₁, L₁⁆ = ⊥)

variable {G : Type u} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- F.6.13 and the concrete ternary image theorem close the case in which
the first local residual lies in a normal three-subgroup of the three-core.
The action kernel's residual-centralization property comes from the actual
supercritical representation in the application. -/
theorem residual_isThreeGroup_of_local_containment
    (source : GoldschmidtRigidityInput.{u})
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (X : Subgroup G) [X.Normal] (hX : IsPGroup 3 X) (hXP : X ≤ pCore 3 G)
    (h₁ : (pResidual 2 G₁).map G₁.subtype ≤ X)
    (f : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (hc : ((pResidual 3 f.ker).map f.ker.subtype) ≤ centralizer (pCore 3 G : Set G)) :
    IsPGroup 3 (pResidual 2 G) := by
  let L₁ := (pResidual 2 G₁).map G₁.subtype
  let L₂ := (pResidual 2 G₂).map G₂.subtype
  by_cases h₂ : L₂ ≤ X
  · exact hX.to_le (h.twoResidual_eq_sup ▸ sup_le h₁ h₂)
  obtain ⟨_, _, _, _, hQE, _, _, hkill, _⟩ := source G G₁ G₂ h hcore X inferInstance h₁ h₂
  let Q := pCore 2 G₂
  let Qa := Q.map G₂.subtype
  let R := pResidual 2 G₂
  let J := (pCore 2 R).map R.subtype
  let Ka := J.map G₂.subtype
  let : IsElementaryAbelian 2 Qa := hQE
  have hJQ : J ≤ Q := le_sSup ⟨inferInstance, pCore_isPGroup.map R.subtype⟩
  have hKaQ : Ka ≤ Qa := map_mono hJQ
  let j : pCore 2 R →* Qa :=
    { toFun := fun x => ⟨x.val.val.val, hKaQ
        (mem_map_of_mem G₂.subtype (mem_map_of_mem R.subtype x.property))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hji : Function.Injective j := by
    intro x y he
    have hh : x.val.val.val = y.val.val.val := congrArg (fun z : Qa => z.val) he
    exact Subtype.ext (Subtype.ext (Subtype.ext hh))
  let : IsElementaryAbelian 2 (pCore 2 R) :=
    { toIsMulCommutative := ⟨⟨fun x y => hji (by simp only [map_mul]; exact IsMulCommutative.is_comm.comm _ _)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => hji (by
        rw [map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 Qa), map_one])) }
  let fR := f.comp (G₂.subtype.comp R.subtype)
  have hKker : pCore 2 R ≤ fR.ker :=
    Matrix.GeneralLinearGroup.three_kills_elementary_twoCore (isPPerfect_pResidual 2)
      (local_residual_quotient_card_three h.quotient_right) fR
  have hKaC : Ka ≤ centralizer (pCore 3 G : Set G) := by
    rintro _ ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    have hxker : x.val.val ∈ f.ker := hKker hx
    let z : f.ker := ⟨x.val.val, hxker⟩
    have hzres : z ∈ pResidual 3 f.ker := by
      apply mem_pResidual_of_orderOf_coprime
      obtain ⟨n, hn⟩ := pCore_isPGroup (p := 2) (G := R) ⟨x, hx⟩
      apply ((by decide : Nat.Coprime 3 2).pow_right n).of_dvd_right
      have he : z ^ (2 ^ n) = 1 := by
        apply Subtype.ext
        exact congrArg (fun w : pCore 2 R => w.val.val.val) hn
      exact orderOf_dvd_of_pow_eq_one he
    exact hc (mem_map_of_mem f.ker.subtype hzres)
  have hKaL : Ka ≤ L₂ := by
    apply map_mono
    exact map_subtype_le _
  have hKaG₂ : Ka ≤ G₂ := hKaL.trans (map_subtype_le _)
  have hKaN : G₂ ≤ normalizer (Ka : Set G) := by
    have hn := J.le_normalizer_map G₂.subtype
    simpa only [J, Ka, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hn
  have hL₁N : L₁ ≤ normalizer (Ka : Set G) :=
    (le_centralizer_iff.mpr (hKaC.trans (centralizer_le (h₁.trans hXP)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hKabot : Ka = ⊥ := by
    have hkill' : (Ka.subgroupOf (Qa ⊔ L₁)).Normal → Ka = ⊥ := by
      simpa only [Ka, J, Qa, Q, R, L₁, map_map] using hkill
    apply hkill'
    apply (normal_subgroupOf_iff_le_normalizer (hKaQ.trans le_sup_left)).mpr
    exact sup_le ((map_subtype_le Q).trans hKaN) hL₁N
  have hKR : pCore 2 R = ⊥ := by
    apply map_injective R.subtype_injective
    apply map_injective G₂.subtype_injective
    simpa only [Subgroup.map_bot] using hKabot
  have hR : IsPGroup 3 R := by
    have hq : IsPGroup 3 (R ⧸ pCore 2 R) :=
      IsPGroup.of_card (n := 1) (local_residual_quotient_card_three h.quotient_right)
    exact hq.of_equiv ((QuotientGroup.quotientMulEquivOfEq hKR).trans QuotientGroup.quotientBot)
  have hjoin : IsPGroup 3 (X ⊔ L₂ : Subgroup G) :=
    hX.to_sup_of_normal_left (hR.map G₂.subtype)
  apply hjoin.to_le
  rw [h.twoResidual_eq_sup]
  exact sup_le (h₁.trans le_sup_left) le_sup_right

/-- The actual supercritical subgroup in a hypothetical non-three-group
branch contains neither local residual. All representation-kernel premises
of the contained case are discharged here. -/
theorem neither_local_residual_le_supercritical
    (source : GoldschmidtRigidityInput.{u})
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hr : primeRank 3 G ≤ 2)
    (X : Subgroup (pCore 3 G)) (hX : IsSupercriticalPSubgroup 3 X)
    (hnot : ¬ IsPGroup 3 (pResidual 2 G)) :
    ¬ (pResidual 2 G₁).map G₁.subtype ≤ X.map (pCore 3 G).subtype ∧
    ¬ (pResidual 2 G₂).map G₂.subtype ≤ X.map (pCore 3 G).subtype := by
  let : X.Characteristic := hX.characteristic
  obtain ⟨j, hj, hc⟩ := supercritical_ternary_action hr X hX
  have hp : IsPGroup 3 (X.map (pCore 3 G).subtype) :=
    (pCore_isPGroup.to_subgroup X).map (pCore 3 G).subtype
  constructor
  · intro h₁
    exact hnot (residual_isThreeGroup_of_local_containment source h hcore _ hp
      (map_subtype_le X) h₁ _ hc)
  · intro h₂
    exact hnot (residual_isThreeGroup_of_local_containment source h.symm hcore _ hp
      (map_subtype_le X) h₂ _ hc)

end CFSG.Quasithin.ChapterF.Noncyclic
