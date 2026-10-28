module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.CartanPanel

/-!
# Faithful panel quotients and Cartan kernels on the source carrier

Let Kᵢ be the core of the whole Borel inside the marked parabolic Pᵢ.
Normality puts Kᵢ inside the reflected Borel, so the actual simple root
meets Kᵢ trivially. Its projection to Pᵢ/Kᵢ is therefore injective.
An element of H ∩ Kᵢ normalizes the simple root and acts trivially after
projection, hence centralizes it. Conjugating within Pᵢ proves the same
for the reflected root and gives [Rᵢ,H ∩ Kᵢ] = 1.

The full panel descends equivariantly through Kᵢ with the original
representative r nᵢ unchanged. These arguments apply to the same finite
marked quotient and require neither local perfectness nor a positive
field parameter. They provide the kernel and centralization steps used
in Fong–Seitz I (3B), p.13, and the proof of (6H)(a), p.51; the rank-one
pairing, common field and remaining (6H) clauses are separate obligations.
-/

@[expose] public noncomputable section
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)

abbrev Endpoint := Q.tits.standardParabolic {Q.simple i}
abbrev endpointBorel : Subgroup (Endpoint Q i) := Q.tits.B.subgroupOf (Endpoint Q i)

def panelKernel : Subgroup (Endpoint Q i) := (endpointBorel Q i).normalCore
instance : (panelKernel Q i).Normal := inferInstanceAs (endpointBorel Q i).normalCore.Normal

def embeddedPanelKernel : Subgroup (X ⧸ Q.D) := (panelKernel Q i).map (Endpoint Q i).subtype

theorem embeddedPanelKernel_le_borel : embeddedPanelKernel Q i ≤ Q.tits.B := by
  rintro x ⟨y,hy,rfl⟩
  exact (endpointBorel Q i).normalCore_le hy

theorem endpoint_normalizes_panelKernel :
    Endpoint Q i ≤ normalizer (embeddedPanelKernel Q i : Set (X ⧸ Q.D)) := by
  intro x hx
  exact (panelKernel Q i).le_normalizer_map (Endpoint Q i).subtype
    ⟨⟨x,hx⟩, (normalizer_eq_top (panelKernel Q i)) ▸ mem_top _, rfl⟩

def reflectionLift : Endpoint Q i :=
  ⟨representative (Q.simple i), Q.tits.bruhatCell_subset_standardParabolic_of_mem
    (Set.mem_singleton _) (Q.tits.representative_mem_bruhatCell _ _ (representative_spec _))⟩

theorem embeddedPanelKernel_le_reflectedBorel :
    embeddedPanelKernel Q i ≤ borelConjugate (Q.simple i) := by
  intro x hx
  have hn := endpoint_normalizes_panelKernel Q i (reflectionLift Q i).property
  exact embeddedPanelKernel_le_borel Q i ((mem_normalizer_iff.mp hn x).mp hx)

theorem simpleRoot_disjoint_panelKernel :
    Disjoint (simpleRoot Q split i) (embeddedPanelKernel Q i) :=
  (simpleRoot_disjoint_conjugateBorel Q split i).mono_right
    (embeddedPanelKernel_le_reflectedBorel Q i)

def rootInEndpoint : simpleRoot Q split i →* Endpoint Q i :=
  inclusion ((simpleRoot_le Q split i).trans
    (split.U_le.trans (Q.tits.B_le_standardParabolic _)))

def rootProjection : simpleRoot Q split i →* (Endpoint Q i ⧸ panelKernel Q i) :=
  (QuotientGroup.mk' (panelKernel Q i)).comp (rootInEndpoint Q split i)

@[simp] theorem rootProjection_apply (r : simpleRoot Q split i) :
    rootProjection Q split i r = QuotientGroup.mk' (panelKernel Q i)
      (⟨r, Q.tits.B_le_standardParabolic _ (split.U_le r.property.1)⟩ : Endpoint Q i) := rfl

theorem rootProjection_injective : Function.Injective (rootProjection Q split i) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro r hr
  have hk : rootInEndpoint Q split i r ∈ panelKernel Q i :=
    (QuotientGroup.eq_one_iff _).mp hr
  have h : (r : X ⧸ Q.D) ∈ embeddedPanelKernel Q i :=
    mem_map_of_mem (Endpoint Q i).subtype hk
  exact Subtype.ext ((disjoint_def.mp (simpleRoot_disjoint_panelKernel Q split i)) r.property h)

/-- A core element normalizing the root centralizes it, because projection is injective. -/
theorem commute_of_panelKernel_of_normalizes {h r : X ⧸ Q.D}
    (hh : h ∈ embeddedPanelKernel Q i)
    (hn : h ∈ normalizer (simpleRoot Q split i : Set (X ⧸ Q.D)))
    (hr : r ∈ simpleRoot Q split i) : Commute h r := by
  have hconj : h*r*h⁻¹ ∈ simpleRoot Q split i := (mem_normalizer_iff.mp hn r).mp hr
  have hP : h ∈ Endpoint Q i := Q.tits.B_le_standardParabolic _
    (embeddedPanelKernel_le_borel Q i hh)
  have hhK : (⟨h,hP⟩ : Endpoint Q i) ∈ panelKernel Q i := by
    obtain ⟨x,hx,he⟩ := hh
    have hxe : x = ⟨h,hP⟩ := Subtype.ext he
    exact hxe ▸ hx
  have hq : QuotientGroup.mk' (panelKernel Q i) ⟨h,hP⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hhK
  have he : h*r*h⁻¹ = r := by
    apply congrArg Subtype.val (rootProjection_injective Q split i (a₁ := ⟨_,hconj⟩)
      (a₂ := ⟨r,hr⟩) ?_)
    change QuotientGroup.mk' (panelKernel Q i)
      ((⟨h,hP⟩ : Endpoint Q i) * rootInEndpoint Q split i ⟨r,hr⟩ * ⟨h,hP⟩⁻¹) = _
    simp only [map_mul, map_inv, hq, one_mul, inv_one, mul_one]
    rfl
  exact mul_inv_eq_iff_eq_mul.mp he

theorem cartanKernel_centralizes_simpleRoot :
    Q.tits.B ⊓ Q.tits.N ⊓ embeddedPanelKernel Q i ≤
      centralizer (simpleRoot Q split i : Set (X ⧸ Q.D)) := by
  intro h hh
  rw [mem_centralizer_iff]
  intro r hr
  exact (commute_of_panelKernel_of_normalizes Q split i hh.2
    (torus_normalizes_simpleRoot Q split i hh.1) hr).symm.eq

/-- The whole rank-one root subgroup uses the selected reflection on the same carrier. -/
def rankOneRootGroup : Subgroup (X ⧸ Q.D) :=
  simpleRoot Q split i ⊔ rightConjugate (simpleRoot Q split i)
    (representative (Q.simple i) : X ⧸ Q.D)

theorem cartanKernel_centralizes_conjugateRoot (n : Q.tits.N)
    (hn : (n : X ⧸ Q.D) ∈ Endpoint Q i) :
    Q.tits.B ⊓ Q.tits.N ⊓ embeddedPanelKernel Q i ≤
      centralizer (rightConjugate (simpleRoot Q split i) (n : X ⧸ Q.D) : Set (X ⧸ Q.D)) := by
  intro h hh
  rw [mem_centralizer_iff]
  intro r hr
  have hH : (n : X ⧸ Q.D)*h*(n : X ⧸ Q.D)⁻¹ ∈ Q.tits.B ⊓ Q.tits.N :=
    (mem_normalizer_iff.mp (torus_normalizes n) h).mp hh.1
  have hK : (n : X ⧸ Q.D)*h*(n : X ⧸ Q.D)⁻¹ ∈ embeddedPanelKernel Q i :=
    (mem_normalizer_iff.mp (endpoint_normalizes_panelKernel Q i hn) h).mp hh.2
  have he := (mem_centralizer_iff.mp
    (cartanKernel_centralizes_simpleRoot Q split i ⟨hH,hK⟩)) _ hr
  apply (MulAut.conj (n : X ⧸ Q.D)).injective
  rw [map_mul, map_mul]
  change (n : X ⧸ Q.D) * r * (n : X ⧸ Q.D)⁻¹ * ((n : X ⧸ Q.D) * h * (n : X ⧸ Q.D)⁻¹) =
    ((n : X ⧸ Q.D) * h * (n : X ⧸ Q.D)⁻¹) * ((n : X ⧸ Q.D) * r * (n : X ⧸ Q.D)⁻¹) at he ⊢
  exact he

/-- The clause [Rᵢ,H ∩ Kᵢ] = 1 needs no rank-one perfectness hypothesis. -/
theorem rankOneRootGroup_commutator_cartanKernel :
    ⁅rankOneRootGroup Q split i, Q.tits.B ⊓ Q.tits.N ⊓ embeddedPanelKernel Q i⁆ = ⊥ := by
  rw [commutator_eq_bot_iff_le_centralizer]
  apply sup_le
  · exact le_centralizer_iff.mp (cartanKernel_centralizes_simpleRoot Q split i)
  · exact le_centralizer_iff.mp (cartanKernel_centralizes_conjugateRoot Q split i
      (representative (Q.simple i)) (reflectionLift Q i).property)

/-- The full Borel in the faithful endpoint quotient, rather than its two-part. -/
def quotientBorel : Subgroup (Endpoint Q i ⧸ panelKernel Q i) :=
  (endpointBorel Q i).map (QuotientGroup.mk' (panelKernel Q i))

theorem quotientBorel_comap :
    (quotientBorel Q i).comap (QuotientGroup.mk' (panelKernel Q i)) = endpointBorel Q i := by
  rw [quotientBorel, comap_map_eq, QuotientGroup.ker_mk']
  exact sup_of_le_left (endpointBorel Q i).normalCore_le

/-- The core quotient preserves the literal entire panel and its action. -/
def panelQuotientEquiv : Panel Q i ≃
    ((Endpoint Q i ⧸ panelKernel Q i) ⧸ quotientBorel Q i) :=
  Theory.CartanPanel.cosetEquiv _ (QuotientGroup.mk'_surjective _) _ _ (quotientBorel_comap Q i)

@[simp] theorem panelQuotientEquiv_mk (x : Endpoint Q i) :
    panelQuotientEquiv Q i (QuotientGroup.mk x) =
      QuotientGroup.mk (QuotientGroup.mk' (panelKernel Q i) x) := rfl

theorem panelQuotientEquiv_smul (x : Endpoint Q i) (c : Panel Q i) :
    panelQuotientEquiv Q i (x • c) =
      QuotientGroup.mk' (panelKernel Q i) x • panelQuotientEquiv Q i c :=
  Theory.CartanPanel.cosetEquiv_smul _ _ _ _ _ x c

/-- On the punctured chart the representative remains the product r nᵢ. -/
theorem panelQuotientEquiv_root (r : simpleRoot Q split i) :
    panelQuotientEquiv Q i
      (simplePanelMap Q split i (representative (Q.simple i)) (representative_spec _) r).val =
    QuotientGroup.mk (rootProjection Q split i r *
      QuotientGroup.mk' (panelKernel Q i) (reflectionLift Q i)) := by
  rw [simplePanelMap_apply]
  rfl

theorem quotientBorel_index :
    (quotientBorel Q i).index = 1 + Nat.card (simpleRoot Q split i) := by
  rw [quotientBorel, index_map_eq _ (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact (endpointBorel Q i).normalCore_le)]
  exact singleton_parabolic_root_index Q split i

/-- A concrete faithful rank-one quotient cannot identify two different source roots. -/
def rootRangeEquiv : simpleRoot Q split i ≃* (rootProjection Q split i).range :=
  MonoidHom.ofInjective (rootProjection_injective Q split i)

@[simp] theorem rootRangeEquiv_apply (r : simpleRoot Q split i) :
    (rootRangeEquiv Q split i r : Endpoint Q i ⧸ panelKernel Q i) = rootProjection Q split i r :=
  MonoidHom.ofInjective_apply _

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
