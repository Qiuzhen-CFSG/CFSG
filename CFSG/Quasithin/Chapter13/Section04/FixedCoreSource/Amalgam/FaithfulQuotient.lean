module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.Generation
public import Theory.GroupTheory.CComponent.PrimeCoreSupplement

/-!
# The full action kernel in the nonsolvable amalgam

The actual component generates X together with T. Its two-core quotient
has trivial three-prime core, so O₃′(X)=O₂(X). Clause (c) makes the full
kernel C_X(V₀) a three-prime group, and reducedness gives the reverse
inclusion O₂(X)≤C_X(V₀). Thus the prime-to-three quotient, the two-core
quotient and the faithful action quotient agree.

The selected component and both local vertices keep their literal
quotient maps. The final result transfers the genuine component and
residual conclusions to X/O₂(X), with the representative formula retained.
Earlier Source1332OneTwo remains an explicit input; no model-selection,
module or Thompson conclusion is assumed here.
Source: Aschbacher–Smith 13.4.7, printed pp.899–900.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V A B : Subgroup G}

/-- In the nonsolvable join the three-prime core is exactly the two-core. -/
theorem original_pair_primeCore_eq_twoCore
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hnonsolv : ¬ Group.IsSolvable (A ⊔ B : Subgroup G)) :
    pPrimeCore 3 (A ⊔ B : Subgroup G) = pCore 2 (A ⊔ B : Subgroup G) := by
  let X := A ⊔ B
  obtain ⟨K,hK⟩ := exists_isCComponent_of_not_isSolvable hnonsolv
  obtain ⟨hn,hf,_,_,_⟩ := original_pair_component_geometry h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK
  let := hn
  have hr := (original_pair_component_is_residual h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK).1
  have hquot : IsPGroup 2 (X ⧸ K) := hr ▸ isPGroup_quotient_pResidual 2
  let C := K.map X.subtype
  let j := K.equivMapOfInjective X.subtype X.subtype_injective
  let e := QuotientGroup.congr (pCore 2 K) (pCore 2 C) j (pCore_map_iso 2 j)
  have hz : pPrimeCore 3 (K ⧸ pCore 2 K) = ⊥ := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [pPrimeCore_map_iso,midSize_primeToThreeCore_eq_bot (h1332 _ hf).2,Subgroup.map_bot]
  exact CComponentExceptionalQuotient.primeCore_eq_twoCore_of_twoGroup_quotient K hquot hz

/-- The entire action kernel equals the two-core, using literal clause (c). -/
theorem original_pair_full_action_kernel
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (hnonsolv : ¬ Group.IsSolvable (A ⊔ B : Subgroup G)) :
    let X := A ⊔ B
    let W := conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) X
    X ⊓ centralizer (W : Set G) = X.pCoreIn 2 := by
  let X := A ⊔ B
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  let W := conjugateSpanBy Z X
  let U := W.subgroupOf X
  let N := centralizer (U : Set X)
  have hWX : W ≤ X := conjugateSpanBy_le (fun z hz =>
    (hTA.trans le_sup_left) ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
      X.le_normalizer
  obtain ⟨hred,_,_,_⟩ := original_pair_action_kernel h₀ D m
    hTA hTB eA eB hne hindexA hindexB
  let : U.Normal := hred.normal
  have hmapN : N.map X.subtype = X ⊓ centralizer (W : Set G) := by
    have hh := map_inf_centralizer_of_injective X.subtype X.subtype_injective
      (⊤ : Subgroup X) (W.subgroupOf X)
    simpa only [top_inf_eq,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le hWX] using hh.symm
  have hcop : Nat.Coprime 3 (Nat.card N) := by
    rw [Nat.card_congr (N.equivMapOfInjective X.subtype X.subtype_injective).toEquiv,hmapN]
    exact original_pair_kernel_primeToThree h₀ D m hTA hTB eA eB hne hindexA hindexB hres
  have hN : N = pCore 2 X := by
    apply le_antisymm
    · exact (show N ≤ pPrimeCore 3 X from le_sSup ⟨inferInstance,hcop⟩).trans_eq
        (original_pair_primeCore_eq_twoCore h₀ D m h1332
          hTA hTB eA eB hne hindexA hindexB hnonsolv)
    · exact le_centralizer_iff.mp hred.le_centralizer_pCore
  exact hmapN.symm.trans (congrArg (Subgroup.map X.subtype) hN)

/-- The original component is the whole residual in the faithful two-core quotient. -/
theorem original_pair_component_twoCore_image
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent) :
    let X := A ⊔ B
    let q := QuotientGroup.mk' (pCore 2 X)
    (q.subgroupMap K).ker = pCore 2 K ∧
      IsComponent (X ⧸ pCore 2 X) (K.map q) ∧ (K.map q).Normal ∧
      (∃ e : (K ⧸ pCore 2 K) ≃* K.map q,
        ∀ k : K, e (QuotientGroup.mk' (pCore 2 K) k) = q.subgroupMap K k) ∧
      pResidual 2 (X ⧸ pCore 2 X) = K.map q ∧
      generalizedFitting (X ⧸ pCore 2 X) = K.map q := by
  have hns : ¬ Group.IsSolvable (A ⊔ B : Subgroup G) := by
    intro hs
    let := hs
    exact hK.not_isSolvable inferInstance
  have he := original_pair_primeCore_eq_twoCore h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB hns
  let P (N : Subgroup (A ⊔ B : Subgroup G)) [N.Normal] : Prop :=
    let q := QuotientGroup.mk' N
    (q.subgroupMap K).ker = pCore 2 K ∧
      IsComponent ((A ⊔ B : Subgroup G) ⧸ N) (K.map q) ∧ (K.map q).Normal ∧
      (∃ e : (K ⧸ pCore 2 K) ≃* K.map q,
        ∀ k : K, e (QuotientGroup.mk' (pCore 2 K) k) = q.subgroupMap K k) ∧
      pResidual 2 ((A ⊔ B : Subgroup G) ⧸ N) = K.map q ∧
      generalizedFitting ((A ⊔ B : Subgroup G) ⧸ N) = K.map q
  have transport {N M : Subgroup (A ⊔ B : Subgroup G)} [N.Normal] [M.Normal]
      (hNM : N = M) : P N → P M := by
    subst M
    exact id
  have hc := original_pair_component_prime_image h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK
  have hr := original_pair_prime_component_is_residual h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK
  exact transport he ⟨hc.1,hc.2.1,hc.2.2.1,hc.2.2.2,hr⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
