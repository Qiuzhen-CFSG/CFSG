module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.PrimeQuotient
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ResidualKernel

/-!
# Equality of the component's action and two-core kernels

Clause (c) makes C_X(V₀) a 3′-group. Its intersection with the selected
component lies in the kernel of the O₃′ quotient, already identified as
O₂(K). Reducedness of V₀ gives the reverse inclusion. Hence the component
acts on V₀ with precisely its two-core as kernel.

The final theorem constructs a component from nonsolvability and assembles
this equality with the actual quotient isomorphism, normality, faithful
local membership, common Sylow image and F.6.10 supplement. No component
or local-structure conclusion is assumed. The remaining 13.4.7 alternatives
and original-L₂ exclusions remain with the source assembly.
Source: Aschbacher–Smith 13.4.7, printed pp.899–900.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V A B : Subgroup G}

/-- The exact component action kernel, retaining clause (c)'s literal cubic residual. -/
theorem original_pair_component_action_kernel
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
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent) :
    let X := A ⊔ B
    let W := conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) X
    let C := K.map X.subtype
    C ⊓ centralizer (W : Set G) = C.pCoreIn 2 := by
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
    have hh := map_inf_centralizer_of_injective X.subtype X.subtype_injective (⊤ : Subgroup X) (W.subgroupOf X)
    simpa only [top_inf_eq,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le hWX] using hh.symm
  have hcopN : Nat.Coprime 3 (Nat.card N) := by
    rw [Nat.card_congr (N.equivMapOfInjective X.subtype X.subtype_injective).toEquiv,hmapN]
    exact original_pair_kernel_primeToThree h₀ D m hTA hTB eA eB hne hindexA hindexB hres
  have hNP : N ≤ pPrimeCore 3 X := le_sSup ⟨inferInstance,hcopN⟩
  have hk := (original_pair_component_prime_image h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK).1
  rw [ker_subgroupMap,QuotientGroup.ker_mk'] at hk
  have hNK : N.comap K.subtype = pCore 2 K := by
    apply le_antisymm ((comap_mono hNP).trans_eq hk)
    rw [pCore_subnormal_eq_comap 2 hK.subnormal]
    exact comap_mono (le_centralizer_iff.mp hred.le_centralizer_pCore)
  have hinf : K ⊓ N = K.pCoreIn 2 := by
    have hh := congrArg (Subgroup.map K.subtype) hNK
    change (N.subgroupOf K).map K.subtype = K.pCoreIn 2 at hh
    rwa [subgroupOf_map_subtype,inf_comm] at hh
  have hh := congrArg (Subgroup.map X.subtype) hinf
  change (K ⊓ centralizer (U : Set X)).map X.subtype = (K.pCoreIn 2).map X.subtype at hh
  rw [←map_inf_centralizer_of_injective X.subtype X.subtype_injective,
    map_subgroupOf_eq_of_le hWX,map_pCoreIn_of_injective 2 _ _ X.subtype_injective] at hh
  exact hh



/-- Nonsolvability constructs a component with both literal quotient and action
kernels, and the genuine F.6.10 residual containment and supplement. -/
theorem exists_original_pair_prime_component
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
    let q := QuotientGroup.mk' (pPrimeCore 3 X)
    let Ap := (A.subgroupOf X).map q
    let Bp := (B.subgroupOf X).map q
    ∃ K : Subgroup X,
      K.IsCComponent ∧ K.Normal ∧
      K.map X.subtype ∈ MainForward.faithfulLocalComponents T ∧
      K.map X.subtype ∈ Chapter1.LStar G T ∧
      K.map X.subtype ⊓ centralizer (W : Set G) = (K.map X.subtype).pCoreIn 2 ∧
      IsComponent (X ⧸ pPrimeCore 3 X) (K.map q) ∧ (K.map q).Normal ∧
      (∃ e : (K ⧸ pCore 2 K) ≃* K.map q,
        ∀ k : K, e (QuotientGroup.mk' (pCore 2 K) k) = q.subgroupMap K k) ∧
      Ap ⊓ Bp = ((T : Subgroup G).subgroupOf X).map q ∧
      ChapterF.IsGoldschmidtTriple Ap Bp ∧
      (((pResidual 2 Ap).map Ap.subtype ≤ K.map q ∧ K.map q ⊔ Bp = ⊤) ∨
        ((pResidual 2 Bp).map Bp.subtype ≤ K.map q ∧ K.map q ⊔ Ap = ⊤)) := by
  obtain ⟨K,hK⟩ := exists_isCComponent_of_not_isSolvable hnonsolv
  obtain ⟨hn,hf,hstar,_,_⟩ := original_pair_component_geometry h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK
  obtain ⟨_,hc,hnp,he⟩ := original_pair_component_prime_image h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK
  obtain ⟨_,hi,ht,_,_,hs⟩ := original_pair_prime_component_supplement h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK
  exact ⟨K,hK,hn,hf,hstar,original_pair_component_action_kernel h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB hres K hK,hc,hnp,he,hi,ht,hs⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
