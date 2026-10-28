module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentMoved
public import Theory.GroupTheory.Commutator.CentralSeedOrbit

/-!
# The full-centralizer orbit of the original central seed

Let H=C_G(z), Z=Ω₁Z(T), U=[⟨Z^K⟩,K], and W=⟨Z^H⟩. The established
component splitting gives W=⟨U^H⟩⟨z⟩ and [W,K]=⟨U^H⟩. Thus its moved
subgroup is normal in H, is fully moved by K, and contains the original U.
The central cyclic factor identifies the two literal action kernels.
Characteristic two and B.2.14 then make both full-orbit subgroups reduced.

ComponentFullCentralizer applies these identities to the natural three-space
and to the original L₁T core. Proving that the larger moved subgroup equals
U is still required for source 13.4.10(7); no irreducibility or equality is
assumed here. The original five-dimensional augmentation marking and the
literal L/centralCore L map are retained. Earlier Chapter12/13.3 inputs
retain their existing producers and final discharge with the fixed-core owner.

Source: Aschbacher--Smith 13.4.10(7), printed p.909, and B.2.14, p.78.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

/-- The full centralizer orbit and its actual K-moved subgroup are reduced.
The latter is precisely the full-centralizer span of the previously constructed
component-moved orbit. Their literal action kernels agree. -/
theorem component_full_orbit
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G)) :
    let H := centralizer ({z.val} : Set G)
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let U := ⁅conjugateSpanBy Z K,K⁆
    let W := conjugateSpanBy Z H
    let Q := ⁅W,K⁆
    IsPReduced 2 (W.subgroupOf H) ∧ IsPReduced 2 (Q.subgroupOf H) ∧
      Q = conjugateSpanBy U H ∧ W = Q ⊔ zpowers z.val ∧
      ⁅Q,K⁆ = Q ∧ Q ≠ ⊥ ∧ U ≤ Q ∧ Q ≤ W ∧
      H ≤ normalizer (Q : Set G) ∧
      H ⊓ centralizer (W : Set G) = H ⊓ centralizer (Q : Set G) := by
  let H := centralizer ({z.val} : Set G)
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := ⁅conjugateSpanBy Z K,K⁆
  let W := conjugateSpanBy Z H
  let Q := ⁅W,K⁆
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  have hTH := Solvable.original_sylow_le_centralizer hzT
  have hTK := hTH.trans hHN
  have hZT : Z ≤ (T : Subgroup G) := fun _ hv => (mem_omegaOneCenterAmbient_iff _ _).mp hv |>.1
  have hZH : Z ≤ H := hZT.trans hTH
  have hsplit := component_seed_split h₀ hzT hz1 hKz hTK
  rw [component_full_fixed_line h structural z.val hz1 hzT hindex K hKz hKM] at hsplit
  obtain ⟨hW,hQ,hmove,hn,hUQ,hQW,hker⟩ := central_seed_overgroup_orbit Z K H U z.val
    hKz hHN le_rfl hzT hZH hsplit (component_moved_eq_commutator h₀ hzT hz1 hKz hTK)
  change Q = conjugateSpanBy U H at hQ
  rw [←hQ] at hW hmove hn hUQ hQW hker
  have hWH : W ≤ H := conjugateSpanBy_le_self hZH
  let : IsElementaryAbelian 2 Z := omegaOneCenterAmbient_elementaryAbelian _
  have hrW : IsPReduced 2 (W.subgroupOf H) := reduced_conjugateSpan_of_sylow_central
    T H Z hTH hZT (fun _ hv => (mem_omegaOneCenterAmbient_iff _ _).mp hv |>.2.2)
    (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (h₀.qtke.evenCharacteristic T)
      (Solvable.centralizer_mem_HOver hzT hz1)))
  have hrQ : IsPReduced 2 (Q.subgroupOf H) := by
    let : (Q.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hn
    let : (W.subgroupOf H).Normal := hrW.normal
    let : IsElementaryAbelian 2 (W.subgroupOf H) := hrW.elementary
    have hc : centralizer (Q.subgroupOf H : Set H) = centralizer (W.subgroupOf H : Set H) := by
      ext x
      constructor
      · intro hx w hw
        have hxQ : x.val ∈ centralizer (Q : Set G) := fun v hv =>
          congrArg Subtype.val (hx ⟨v,(hQW.trans hWH) hv⟩ hv)
        have hxW := hker.symm ▸ show x.val ∈ H ⊓ centralizer (Q : Set G) from ⟨x.property,hxQ⟩
        exact Subtype.ext (hxW.2 w.val hw)
      · intro hx v hv
        exact hx v (hQW hv)
    refine ⟨inferInstance,IsElementaryAbelian.of_le (show Q.subgroupOf H ≤ W.subgroupOf H from comap_mono hQW),?_⟩
    let e := QuotientGroup.quotientMulEquivOfEq hc
    apply (map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
    rw [pCore_map_iso 2 e]
    exact hrW.quotient_pCore_eq_bot
  exact ⟨hrW,hrQ,hQ,hW,hmove,
    fun he => component_moved_ne_bot h structural m hKM (bot_unique (hUQ.trans_eq he)),
    hUQ,hQW,hn,hker⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
