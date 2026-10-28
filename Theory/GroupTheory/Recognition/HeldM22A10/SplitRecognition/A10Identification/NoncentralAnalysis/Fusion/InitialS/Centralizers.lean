module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.InitialS.WeakClosure
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Terminal.LocalCentralizers
public import Theory.GroupTheory.CentralizerSylowConjugacy

/-!
# Centralizer Sylows under Held's contrary S-fusion assumption

Weak closure places every two-subgroup containing S in its displayed
normalizer. Hence a local two-group centralizer containing S is already a
Sylow subgroup of the full ambient centralizer. Fusion between such elements
would identify their local centralizers. Their orders and center orders
therefore separate lambda from mu and tau, as required in Held 2.9.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 2.9, printed pp.229--230.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.InitialS
open Coordinates
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

omit [Finite G] in
private theorem local_centralizer_map (x : H) :
    (centralizer ({x} : Set H)).map (D.a10ModelEmbedding e) =
      D.centralizer ⊓ centralizer ({D.a10ModelEmbedding e x} : Set G) := by
  let f := D.a10ModelEmbedding e
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(e.symm a).property, mem_centralizer_singleton_iff.mpr ?_⟩
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp ha)
  · rintro ⟨hy, hc⟩
    have hyr : y ∈ f.range := by rwa [D.a10ModelEmbedding_range e]
    obtain ⟨a, rfl⟩ := hyr
    refine ⟨a, mem_centralizer_singleton_iff.mpr ?_, rfl⟩
    apply D.a10ModelEmbedding_injective e
    simpa only [map_mul] using mem_centralizer_singleton_iff.mp hc

public theorem exists_sylow_eq_local_centralizer (h : Separated D e) (x : H)
    (hS : modelS ≤ centralizer ({x} : Set H))
    (hp : IsPGroup 2 (centralizer ({x} : Set H))) :
    ∃ P : Sylow 2 (centralizer ({D.a10ModelEmbedding e x} : Set G)),
      (P : Subgroup _).map (centralizer ({D.a10ModelEmbedding e x} : Set G)).subtype =
        (centralizer ({x} : Set H)).map (D.a10ModelEmbedding e) := by
  let C := centralizer ({D.a10ModelEmbedding e x} : Set G)
  let K := (centralizer ({x} : Set H)).map (D.a10ModelEmbedding e)
  have hKC : K ≤ C := (local_centralizer_map D e x).le.trans inf_le_right
  have hKp : IsPGroup 2 K := hp.map _
  have hKpC : IsPGroup 2 (K.subgroupOf C) :=
    hKp.of_equiv (subgroupOfEquivOfLe hKC).symm
  obtain ⟨P, hKP⟩ := hKpC.exists_le_sylow
  let R := (P : Subgroup C).map C.subtype
  have hKR : K ≤ R := by
    rw [← map_subgroupOf_eq_of_le hKC]
    exact map_mono hKP
  have hSR : ambientElementary D e 1 ≤ R := (map_mono hS).trans hKR
  have hRN := two_subgroup_le_normalizer_S D e h R (P.isPGroup'.map C.subtype) hSR
  rw [normalizer_S_eq D e h] at hRN
  have hRH : R ≤ D.centralizer := by
    have hRD := hRN.trans (map_le_range (f := D.a10ModelEmbedding e) modelD)
    rwa [D.a10ModelEmbedding_range e] at hRD
  refine ⟨P, le_antisymm ?_ hKR⟩
  change R ≤ K
  rw [show K = D.centralizer ⊓ C from local_centralizer_map D e x]
  exact le_inf hRH (map_subtype_le _)

/-- Fusion in S identifies its local two-group centralizers under the contrary assumption. -/
public theorem local_centralizers_equiv_of_isConj (h : Separated D e) (x y : H)
    (hx : modelS ≤ centralizer ({x} : Set H))
    (hy : modelS ≤ centralizer ({y} : Set H))
    (hxp : IsPGroup 2 (centralizer ({x} : Set H)))
    (hyp : IsPGroup 2 (centralizer ({y} : Set H)))
    (hf : IsConj (D.a10ModelEmbedding e x) (D.a10ModelEmbedding e y)) :
    Nonempty (centralizer ({x} : Set H) ≃* centralizer ({y} : Set H)) := by
  obtain ⟨P, hP⟩ := exists_sylow_eq_local_centralizer D e h x hx hxp
  obtain ⟨Q, hQ⟩ := exists_sylow_eq_local_centralizer D e h y hy hyp
  obtain ⟨g, _, hg⟩ := Sylow.exists_conj_element_and_centralizer_sylow _ _ hf P Q
  rw [hP, hQ] at hg
  let f := D.a10ModelEmbedding e
  let K := (centralizer ({x} : Set H)).map f
  let L := (centralizer ({y} : Set H)).map f
  let c : K ≃* L :=
    (K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr hg)
  exact ⟨((centralizer ({x} : Set H)).equivMapOfInjective f
    (D.a10ModelEmbedding_injective e)).trans (c.trans
      ((centralizer ({y} : Set H)).equivMapOfInjective f
        (D.a10ModelEmbedding_injective e)).symm)⟩

private theorem S_le_lam_centralizer : modelS ≤ centralizer ({lam} : Set H) := by
  rw [show centralizer ({lam} : Set H) = terminalLocalCentralizer 0 from rfl,
    terminalLocalCentralizer_eq]
  exact le_sup_left

private theorem S_le_tau_centralizer : modelS ≤ centralizer ({tau} : Set H) := by
  rw [show centralizer ({tau} : Set H) = terminalLocalCentralizer 1 from rfl,
    terminalLocalCentralizer_eq]
  exact le_sup_left

private theorem lam_centralizer_two : IsPGroup 2 (centralizer ({lam} : Set H)) :=
  IsPGroup.of_card (n := 5) (terminalLocalCentralizer_card 0)

private theorem tau_centralizer_two : IsPGroup 2 (centralizer ({tau} : Set H)) :=
  IsPGroup.of_card (n := 5) (terminalLocalCentralizer_card 1)

public theorem lambda_mu_nonfusion (h : Separated D e) :
    ¬ IsConj (D.a10ModelEmbedding e lam) (D.a10NoncentralInvolution e) := by
  intro hf
  obtain ⟨c⟩ := local_centralizers_equiv_of_isConj D e h lam mu S_le_lam_centralizer
    (elementary_le_centralizer_mu 1) lam_centralizer_two
    (IsPGroup.of_card (n := 6) centralizer_mu_card) hf
  have hc := Nat.card_congr c.toEquiv
  rw [centralizer_mu_card] at hc
  have hl : Nat.card (centralizer ({lam} : Set H)) = 32 := terminalLocalCentralizer_card 0
  omega

public theorem lambda_tau_nonfusion (h : Separated D e) :
    ¬ IsConj (D.a10ModelEmbedding e lam) (D.a10ModelEmbedding e tau) := by
  intro hf
  obtain ⟨c⟩ := local_centralizers_equiv_of_isConj D e h lam tau S_le_lam_centralizer
    S_le_tau_centralizer lam_centralizer_two tau_centralizer_two hf
  have hc := Nat.card_congr (centerCongr c).toEquiv
  have hl : Nat.card (center (centralizer ({lam} : Set H))) = 8 :=
    terminalLocalCentralizer_center_card 0
  have ht : Nat.card (center (centralizer ({tau} : Set H))) = 4 :=
    terminalLocalCentralizer_center_card 1
  omega

private theorem piLambda_centralizer :
    centralizer ({pi * lam} : Set H) = centralizer ({lam} : Set H) := by
  ext x
  simp only [mem_centralizer_singleton_iff]
  have hp := mem_center_iff.mp modelCentralInvolution_mem_center x
  change x * pi = pi * x at hp
  rw [← mul_assoc, hp, mul_assoc, mul_assoc, mul_left_cancel_iff]

public theorem piLambda_mu_nonfusion (h : Separated D e) :
    ¬ IsConj (D.a10ModelEmbedding e (pi * lam)) (D.a10NoncentralInvolution e) := by
  intro hf
  obtain ⟨c⟩ := local_centralizers_equiv_of_isConj D e h (pi * lam) mu
    (piLambda_centralizer.symm ▸ S_le_lam_centralizer)
    (elementary_le_centralizer_mu 1) (piLambda_centralizer.symm ▸ lam_centralizer_two)
    (IsPGroup.of_card (n := 6) centralizer_mu_card) hf
  have hc := Nat.card_congr c.toEquiv
  rw [centralizer_mu_card, piLambda_centralizer] at hc
  have hl : Nat.card (centralizer ({lam} : Set H)) = 32 := terminalLocalCentralizer_card 0
  omega

public theorem piLambda_tau_nonfusion (h : Separated D e) :
    ¬ IsConj (D.a10ModelEmbedding e (pi * lam)) (D.a10ModelEmbedding e tau) := by
  intro hf
  obtain ⟨c⟩ := local_centralizers_equiv_of_isConj D e h (pi * lam) tau
    (piLambda_centralizer.symm ▸ S_le_lam_centralizer)
    S_le_tau_centralizer (piLambda_centralizer.symm ▸ lam_centralizer_two) tau_centralizer_two hf
  have hc := Nat.card_congr (centerCongr c).toEquiv
  rw [piLambda_centralizer] at hc
  have hl : Nat.card (center (centralizer ({lam} : Set H))) = 8 :=
    terminalLocalCentralizer_center_card 0
  have ht : Nat.card (center (centralizer ({tau} : Set H))) = 4 :=
    terminalLocalCentralizer_center_card 1
  omega

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.InitialS
