module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalInterfaces
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
public import Theory.GroupTheory.PResidual.PrimeToIntersection

/-!
# The literal omega-center seed for the terminal local product

The selected nonidentity central involution belongs to Y and is fixed by
each of K, L₂ and T. Thus Y has nontrivial two-core and characteristic two.
B.2.14 then makes the actual orbit U=⟨Z^Y⟩ reduced; in particular U lies
in O₂(Y) and O₂(Y) centralizes U. No product quotient is assumed.

The residual comparison also identifies O^{3′}(C_L(Z)) with
O^{3′}(C_G(Z)), conditional only on the still separate source identity
L=O^{3′}(N_G(L)). All subgroups retain their ambient embeddings.
Source: Aschbacher--Smith, 12.3.13 and completion of 12.3.1, pp.811--812.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable {S : Setup T L V} {D : S.LocalAnalysis}
namespace TerminalPoint
variable (P : TerminalPoint S D)

theorem Le_le_pointCentralizer : P.Le ≤ P.pointCentralizer :=
  (map_subtype_le _).trans inf_le_right

theorem L2_le_Le : P.L2 ≤ P.Le :=
  (map_subtype_le _).trans inf_le_left

theorem L2_le_quotientCentralizer : P.L2 ≤ P.quotientCentralizer :=
  (map_subtype_le _).trans inf_le_right

theorem sylow_le_Y : (T : Subgroup G) ≤ P.Y := le_sup_right

/-- Every generator of the literal local product fixes the selected point. -/
theorem Y_le_pointCentralizer : P.Y ≤ P.pointCentralizer := by
  apply sup_le (sup_le ((map_subtype_le _).trans P.centralizes)
    (P.L2_le_Le.trans P.Le_le_pointCentralizer))
  intro t ht
  exact mem_centralizer_singleton_iff.mpr
    (((mem_omegaCenterIn_iff _ _).mp P.central).2.1 t ht)

/-- The selected central involution witnesses the nontrivial core of Y. -/
theorem Y_twoCore_ne_bot : P.Y.pCoreIn 2 ≠ ⊥ := by
  have heT : (P.point : G) ∈ (T : Subgroup G) :=
    ((mem_omegaCenterIn_iff _ _).mp P.central).1
  have ho : orderOf (P.point : G) = 2 :=
    orderOf_eq_prime ((mem_omegaCenterIn_iff _ _).mp P.central).2.2
      (fun h => P.nonidentity (Subtype.ext h))
  have hp : IsPGroup 2 (zpowers (P.point : G)) :=
    IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers, pow_one] using ho)
  have hzY : zpowers (P.point : G) ≤ P.Y := zpowers_le.mpr (P.sylow_le_Y heT)
  have hn : P.Y ≤ normalizer (zpowers (P.point : G) : Set G) := by
    apply P.Y_le_pointCentralizer.trans
    change centralizer ({(P.point : G)} : Set G) ≤ _
    rw [← centralizer_closure, ← zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer _
  have hcore := le_pCoreIn_of_normalizes hp hzY hn
  intro he
  exact P.nonidentity (Subtype.ext
    (mem_bot.mp (he ▸ hcore (mem_zpowers (P.point : G)))))

/-- Characteristic two follows from the original ambient condition (E). -/
theorem Y_characteristicTwo : HasCharacteristicTwo P.Y :=
  Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
    (S.hypothesis.simpleQTKE.evenCharacteristic T)
    ⟨P.Y_twoCore_ne_bot, P.sylow_le_Y⟩)

theorem Z_le_Y : P.Z ≤ P.Y := by
  intro z hz
  exact P.sylow_le_Y ((mem_omegaCenterIn_iff _ _).mp hz).1

theorem U_le_Y : P.U ≤ P.Y :=
  (componentOrbit_le_sup P.Z P.Y).trans (sup_le P.Z_le_Y le_rfl)

omit [Finite G] in
private theorem orbit_eq_span (A H : Subgroup G) :
    componentOrbit A H = conjugateSpanBy A H := by
  apply le_antisymm
  · exact iSup_conjugates_le_of_le_normalizer A H _
      (le_conjugateSpanBy A H) (le_normalizer_conjugateSpanBy A H)
  · exact conjugateSpanBy_le (le_componentOrbit A H) (le_normalizer_componentOrbit A H)

/-- The reducedness field of ProductAnalysis, proved before either factor
recognition or the product quotient. -/
theorem U_reduced : IsPReduced 2 (P.U.subgroupOf P.Y) := by
  let R : Sylow 2 P.Y := T.subtype P.sylow_le_Y
  have hz : Stellmacher.omegaOneCenterAmbient (R : Subgroup P.Y) =
      P.Z.subgroupOf P.Y := by
    apply map_injective P.Y.subtype_injective
    rw [← Stellmacher.omegaOneCenterAmbient_map_injective P.Y.subtype P.Y.subtype_injective,
      map_subgroupOf_eq_of_le P.Z_le_Y]
    change Stellmacher.omegaOneCenterAmbient
      (((T : Subgroup G).subgroupOf P.Y).map P.Y.subtype) = P.Z
    rw [map_subgroupOf_eq_of_le P.sylow_le_Y]
    rfl
  have hr := omegaCenter_normalClosure_reduced R P.Y_characteristicTwo
  rw [hz, normalClosure_subgroupOf_eq_conjugateSpanBy _ _ P.Z_le_Y,
    ← orbit_eq_span] at hr
  exact hr

theorem U_le_twoCore : P.U ≤ P.Y.pCoreIn 2 := by
  have h := map_mono (f := P.Y.subtype) P.U_reduced.le_pCore
  rwa [map_subgroupOf_eq_of_le P.U_le_Y] at h

/-- One inclusion in the required equality C_Y(U)=O₂(Y) is unconditional. -/
theorem twoCore_le_U_centralizer : P.Y.pCoreIn 2 ≤ P.Y ⊓ centralizer (P.U : Set G) := by
  refine le_inf (map_subtype_le _) ?_
  apply le_centralizer_iff.mp
  have h := (map_mono (f := P.Y.subtype) P.U_reduced.le_centralizer_pCore).trans
    (map_centralizer_le_centralizer_image _ _)
  rwa [map_subgroupOf_eq_of_le P.U_le_Y] at h

/-- The literal quotient-action kernel makes the two factors commute
modulo the two-core of K. This uses the original action, not an abstract
identification of either factor. -/
theorem factor_commutator_le_K_twoCore : ⁅P.K, P.L2⁆ ≤ P.K.pCoreIn 2 := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro a ha k hk
  obtain ⟨b, hb, rfl⟩ := P.L2_le_quotientCentralizer ha
  have hf : quotientAut (pCore 2 P.K) (P.K.normalizerMonoidHom b) = 1 := hb
  have he := DFunLike.congr_fun hf (QuotientGroup.mk' (pCore 2 P.K) ⟨k, hk⟩)
  rw [quotientAut_apply_mk] at he
  have hc : P.K.normalizerMonoidHom b ⟨k, hk⟩ / ⟨k, hk⟩ ∈ pCore 2 P.K :=
    QuotientGroup.eq_iff_div_mem.mp he
  simpa only [pCoreIn, commutatorElement_def, div_eq_mul_inv, map_mul, map_inv,
    subtype_apply, normalizerMonoidHom_apply_apply_coe] using mem_map_of_mem P.K.subtype hc

/-- The two factor images in Y/O₂(Y) commute, using only the relative
normality conclusion of the component analysis. -/
theorem factor_commutator_le_Y_twoCore (C : P.ComponentAnalysis) :
    ⁅P.K, P.L2⁆ ≤ P.Y.pCoreIn 2 :=
  P.factor_commutator_le_K_twoCore.trans
    (pCoreIn_mono_of_normalizes (le_sup_left.trans le_sup_left)
      (P.Y_le_pointCentralizer.trans C.normalizes))

/-- The ambient prime-to-three centralizer residual has the original
L₁ embedding once 12.3.13 supplies the normalizer residual identity. -/
theorem L1_eq_ambient_residual
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (hres : (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L) :
    P.L1 = (primeToResidual 3 (centralizer (P.Z : Set G))).map
      (centralizer (P.Z : Set G)).subtype := by
  have he := embedded_primeToResidual_intersection 3 (normalizer (L : Set G))
    (centralizer (P.Z : Set G))
  rw [hres, inf_eq_right.mpr (omega_center_centralizer_le S D structural)] at he
  exact he

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
