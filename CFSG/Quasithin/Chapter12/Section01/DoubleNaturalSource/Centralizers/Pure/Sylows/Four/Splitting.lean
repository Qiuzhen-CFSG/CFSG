module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.OmegaModule
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.XiFixed
public import Theory.Representation.BinaryConjugationSection.FixedSplitting
public import Theory.Representation.BinaryNaturalDual.FirstCohomology

/-!
# The full omega module and the source fixed-subgroup comparison

The sharp offender calculation puts every L-displacement of Omega1(Z(Q))
in the actual doubled module W. The original O2(L) lies in Q and centralizes
this whole omega center. The displacement cocycle therefore descends through
the given L/O2(L) marking. Vanishing H1 for the binary natural-plus-dual
module gives Omega1(Z(Q)) = W C_{Omega1(Z(Q))}(L).

The already constructed X <= L has C_W(X)=1, so the splitting identifies
its fixed subgroup with the L-fixed subgroup. The actual point omega center
Z1 is contained in Omega1(Z(Q)); restriction yields C_Z1(X)=C_Z1(L).
This supplies the consequence of the source B.5.1 splitting directly on a
larger explicit elementary subgroup, without requiring an identification of
R2(LQ). The contrary-Sylow application discharges Thompson movement.
No MS conclusion is assumed. XiNonnormal consumes this identity; the original
MS fixed-subgroup nontriviality and terminal component exclusions remain with
qt-d-double-natural-pure-fusion and the existing qt-rank-two-ms93 producer.
Source: Aschbacher--Smith 12.1.4, printed p.790, and I.1.6(6), p.408.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The full core omega center splits over the literal doubled orbit. -/
theorem doubleNatural_four_core_omega_split
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ _ : B.SourceModel,
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 →
      omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) =
        componentOrbit V (T : Subgroup G) ⊔
          (omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) ⊓ centralizer (L : Set G)) := by
  let := D.doubledOrbit_elementary h
  intro S hm
  let H := L ⊔ (T : Subgroup G)
  let W := componentOrbit V (T : Subgroup G)
  let U := omegaCenterIn (H.pCoreIn 2)
  let ρ := BinaryNaturalDual.naturalDualRepresentation
    (V := BinaryLinear.OuterCyclic.Space 4)
  let : Subsingleton (Representation.OneCohomology.H1 ρ) :=
    BinaryNaturalDual.naturalDual_H1_subsingleton (by decide : 4 ≤ 4)
  let q : L →* BinaryLinear.OuterCyclic.LinearGroup 4 :=
    B.component.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := B.component.surjective.comp (QuotientGroup.mk'_surjective _)
  have hWL : W ≤ L := by
    apply iSup_le
    intro t
    rintro _ ⟨v,hv,rfl⟩
    exact (D.sylow_normalizes_component t.property v).mp (D.le_component hv)
  have hLW : L ≤ normalizer (W : Set G) := by
    dsimp [W]
    rw [B.orbit_eq]
    exact L.le_normalizer.trans (le_normalizer_componentOrbit _ _)
  let d : BinaryConjugationSection L W ⊥ (ρ.comp q) := {
    section_le := hWL
    kernel_le := bot_le
    normalized := hLW
    coordinates := B.coordinates.toMonoidHom
    onto := B.coordinates.surjective
    kernel_eq := by
      ext w
      change B.coordinates w = 1 ↔ (w : G) = 1
      rw [B.coordinates.map_eq_one_iff]
      exact Subtype.ext_iff
    equivariant := by
      intro l w
      change (B.coordinates ⟨(l : G) * w * (l : G)⁻¹,_⟩).toAdd =
        ρ (q l) (B.coordinates w).toAdd
      have he : (⟨(l : G) * w * (l : G)⁻¹,(hLW l.property w).mp w.property⟩ : W) =
          B.coordinates.symm (Multiplicative.ofAdd (ρ (q l) (B.coordinates w).toAdd)) :=
        Subtype.ext (B.component_action l w).symm
      rw [he,B.coordinates.apply_symm_apply,toAdd_ofAdd] }
  have hc := D.doubleNatural_four_core_omega_commutator_le h B S hm
  have hk : ∀ l ∈ q.ker, ∀ x ∈ U, ⁅(l : G),x⁆ ∈ (⊥ : Subgroup G) := by
    intro l hl x hx
    have hlQ : l ∈ pCore 2 L := by
      apply (QuotientGroup.eq_one_iff l).mp
      exact B.component.injective (show B.component (QuotientGroup.mk' _ l) = B.component 1 from
        (show q l = 1 from hl).trans B.component.map_one.symm)
    have hlH : (l : G) ∈ H.pCoreIn 2 :=
      pCoreIn_mono_of_normalizes le_sup_left
        (sup_le L.le_normalizer D.sylow_normalizes_component) (mem_map_of_mem L.subtype hlQ)
    exact mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr
      (((mem_omegaCenterIn_iff _ _).mp hx).2.1 l hlH))
  have hWU := D.doubledOrbit_le_core_omega h
  apply le_antisymm ?_ (sup_le hWU inf_le_left)
  intro x hx
  obtain ⟨w,hw⟩ := d.exists_fixed_mod_kernel q hq U
    (by rw [commutator_comm]; exact hc) hk ⟨x,hx⟩
  have hf : (w : G)⁻¹ * x ∈ U ⊓ centralizer (L : Set G) := by
    refine ⟨U.mul_mem (U.inv_mem (hWU w.property)) hx,?_⟩
    intro l hl
    exact commutatorElement_eq_one_iff_mul_comm.mp (mem_bot.mp (hw ⟨l,hl⟩))
  have he := mul_mem_sup w.property hf
  simpa only [mul_inv_cancel_left] using he

/-- The original contrary ambient-Sylow branch discharges every splitting premise. -/
theorem doubleNatural_four_pure_core_omega_split_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) =
        componentOrbit V (T : Subgroup G) ⊔
          (omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) ⊓ centralizer (L : Set G)) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf
  exact D.doubleNatural_four_core_omega_split h B S
    (D.doubleNatural_four_pure_thompson_moves_of_many h hmany B S w hw hp hfix hf).1
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
variable {G : Type*} [Group G]

private theorem fixed_eq_of_split (U W L X : Subgroup G) [IsMulCommutative U]
    (hX : X ≤ L) (hs : U = W ⊔ (U ⊓ centralizer (L : Set G)))
    (hfix : W ⊓ centralizer (X : Set G) = ⊥) :
    U ⊓ centralizer (X : Set G) = U ⊓ centralizer (L : Set G) := by
  have hWL : W ≤ U := by rw [hs]; exact le_sup_left
  apply le_antisymm ?_ (inf_le_inf_left _ (centralizer_le hX))
  intro x hx
  have hn : U ⊓ centralizer (L : Set G) ≤ normalizer (W : Set G) := by
    exact (inf_le_left.trans (U.le_centralizer.trans (centralizer_le hWL))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hm : x ∈ (W : Set G) * ((U ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ hn,←hs]
    exact hx.1
  obtain ⟨w,hw,c,hc,rfl⟩ := hm
  have hwX : w ∈ centralizer (X : Set G) := by
    have hcX := centralizer_le hX hc.2
    have hh := (centralizer (X : Set G)).mul_mem hx.2 ((centralizer _).inv_mem hcX)
    simpa only [mul_inv_cancel_right] using hh
  have hw1 : w = 1 := mem_bot.mp (hfix ▸ (show w ∈ W ⊓ centralizer (X : Set G) from ⟨hw,hwX⟩))
  change w * c ∈ U ⊓ centralizer (L : Set G)
  rw [hw1,one_mul]
  exact hc
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- X and L have exactly the same fixed subgroup in the full core omega center. -/
theorem doubleNatural_four_core_omega_xi_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ _ : B.SourceModel,
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 →
      omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) ⊓
          centralizer (PureFourXi.residual T L : Set G) =
        omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) ⊓ centralizer (L : Set G) := by
  let := D.doubledOrbit_elementary h
  intro S hm
  apply PureFourXi.fixed_eq_of_split _ (componentOrbit V (T : Subgroup G)) _ _
    (PureFourXi.residual_le_component T L h.maximal_faithful.2.1.2.1 D.sylow_normalizes_component)
    (D.doubleNatural_four_core_omega_split h B S hm)
  apply S.four_xi_centralizer_eq_bot D.sylow_normalizes_component (D.doubledOrbit_E322 h).le_sylow
  intro hc
  apply hm
  rw [←D.doubledOrbit_sylow_centralizer h]
  exact le_inf (sSup_le fun _ hA => hA.1) hc

/-- The point omega center is inside the core omega center, with the actual point retained. -/
theorem doubleNatural_point_omega_le_core_omega
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n)
    (w : componentOrbit V (T : Subgroup G)) :
    omegaCenterIn (B.pointSylow w) ≤ omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let := D.doubledOrbit_elementary h
  let W := componentOrbit V (T : Subgroup G)
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let R := B.pointSylow w
  have hWR : W ≤ R := by
    intro v hv
    exact ⟨(D.doubledOrbit_E322 h).le_sylow hv,
      mem_centralizer_singleton_iff.mpr (W.le_centralizer hv w w.property).symm⟩
  have hQR : Q ≤ R := by
    dsimp only [Q]
    rw [←D.doubledOrbit_sylow_centralizer h]
    intro x hx
    exact ⟨hx.1,mem_centralizer_singleton_iff.mpr (hx.2 w w.property).symm⟩
  intro x hx
  obtain ⟨hxR,hc,hs⟩ := (mem_omegaCenterIn_iff R x).mp hx
  apply (mem_omegaCenterIn_iff Q x).mpr
  refine ⟨?_,centralizer_le hQR hc,hs⟩
  dsimp only [Q]
  rw [←D.doubledOrbit_sylow_centralizer h]
  exact ⟨hxR.1,centralizer_le hWR hc⟩

/-- Restriction gives the source identity C_Z1(X)=C_Z1(L), without MS classification. -/
theorem doubleNatural_four_point_omega_xi_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ _ : B.SourceModel,
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 →
      ∀ w : componentOrbit V (T : Subgroup G),
        omegaCenterIn (B.pointSylow w) ⊓ centralizer (PureFourXi.residual T L : Set G) =
          omegaCenterIn (B.pointSylow w) ⊓ centralizer (L : Set G) := by
  let := D.doubledOrbit_elementary h
  intro S hm w
  have he := D.doubleNatural_four_core_omega_xi_fixed h B S hm
  have hle := D.doubleNatural_point_omega_le_core_omega h B w
  calc
    _ = omegaCenterIn (B.pointSylow w) ⊓
        (omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) ⊓
          centralizer (PureFourXi.residual T L : Set G)) := by rw [←inf_assoc,inf_eq_left.mpr hle]
    _ = _ := by rw [he,←inf_assoc,inf_eq_left.mpr hle]
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

