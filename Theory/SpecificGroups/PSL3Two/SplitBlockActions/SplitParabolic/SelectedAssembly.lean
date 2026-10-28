module

public import Theory.SpecificGroups.PSL3Two.SplitBlockActions.SplitParabolic.NaturalIdentification.Transport
public import Theory.SpecificGroups.PSL3Two.SplitBlockActions.SplitParabolic.OutsideSelection.Geometry

/-!
# The selected involution in the genuinely flagged split block

The natural Sylow identification discharges both coordinate premises of
OutsideSelection. The actual conjugate of C_U(V₂) supplements U to the
flagged Sylow, and a root involution supplies an outside representative.
Its action on the original quaternion core has the a₂ square-quotient
condition, and it generates the elementary Thompson subgroup with [U,x].

All relative centralizers, conjugates, and actions are transported through
an arbitrary injective block homomorphism. The central point is identified
as the unique nonidentity central element of the unitriangular group.

The selection is existential for each permitted g. Outside membership alone
does not imply that every representative is an involution; the order-four
example in Unitriangular remains applicable. This does not refute the full
ambient theorem, whose other hypotheses are not imposed on the model.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 12.8.9,
printed pp.852–853, and proof of 14.4.4, printed p.1007.
-/

@[expose] public section

open Subgroup
namespace Matrix.PSL3Two.SplitParabolic.SelectedAssembly
open OutsideSelection

theorem coreCoordinates : CoreCoordinates := by
 intro x
 rw [OutsideSelection.U, ← SplitParabolic.U_image]
 constructor
 · rintro ⟨y,hy,rfl⟩
   exact ⟨sylowMap_mem y, hy⟩
 · rintro ⟨hx,hu⟩
   exact ⟨recover x,hu,sylowMap_recover x hx⟩

theorem coreIdentification : Unitriangular.U.map (sylowEmbedding sylowEquiv) = OutsideSelection.U :=
 SplitParabolic.U_image

/-- Both identification premises of the outside-selection calculation are now discharged. -/
theorem selected_geometry (g : Block) (hg : g ∈ linePreimage) (hp : g ∉ pointPreimage)
 (d : QuaternionCentralProductData OutsideSelection.U) :
 zpowers (selected g) ⊔ ⁅OutsideSelection.U,zpowers (selected g)⁆ =
   Stellmacher.elementaryAbelianMaxJ standardSylow ∧
 ∃ hn : selected g ∈ normalizer (OutsideSelection.U : Set Block),
   d.IsA2Action (OutsideSelection.U.normalizerMonoidHom ⟨selected g,hn⟩) :=
 selected_generation_and_a2 sylowEquiv coreIdentification coreCoordinates g hg hp d

/-- The nontrivial central element is fixed by the unitriangular marking. -/
theorem central_nonidentity (x : Unitriangular.T)
 (hx : x ∈ center Unitriangular.T) (hne : x ≠ 1) : x = Unitriangular.z := by
 have h := mem_center_iff.mp hx
 exact (by decide +kernel : ∀ x : Unitriangular.T,
  Unitriangular.r*x=x*Unitriangular.r → Unitriangular.q*x=x*Unitriangular.q →
  Unitriangular.a*x=x*Unitriangular.a → x ≠ 1 → x=Unitriangular.z)
   x (h _) (h _) (h _) hne

/-- Any element outside the index-two core supplements it. -/
theorem core_sup_outside (x : Unitriangular.T) (hx : x ∉ Unitriangular.U) :
 Unitriangular.U ⊔ zpowers x = ⊤ := by
 apply top_unique
 intro y _
 by_cases hy : y ∈ Unitriangular.U
 · exact (show Unitriangular.U ≤ Unitriangular.U ⊔ zpowers x from le_sup_left) hy
 · have hbit : y.x23 + x.x23 = 0 :=
    (by decide : ∀ a b : ZMod 2, a ≠ 0 → b ≠ 0 → a+b=0) _ _ hy hx
   have hprod : y*x⁻¹ ∈ Unitriangular.U := hbit
   have h1 : y*x⁻¹ ∈ Unitriangular.U ⊔ zpowers x := (show Unitriangular.U ≤ Unitriangular.U ⊔ zpowers x from le_sup_left) hprod
   have h2 : x ∈ Unitriangular.U ⊔ zpowers x := (show zpowers x ≤ Unitriangular.U ⊔ zpowers x from le_sup_right) (mem_zpowers x)
   simpa only [inv_mul_cancel_right] using (Unitriangular.U ⊔ zpowers x).mul_mem h1 h2

/-- The actual conjugate centralizer supplements the core to the flagged Sylow. -/
theorem core_sup_conjugate (g : Block) (hg : g ∈ linePreimage) (hp : g ∉ pointPreimage) :
 OutsideSelection.U ⊔ OutsideSelection.X g = standardSylow := by
 let y := recover (selected g)
 have hy : sylowMap y = selected g :=
  sylowMap_recover _ (conjugate_le_sylow coreCoordinates g hg (selected_mem coreCoordinates g))
 have hu : y ∉ Unitriangular.U := by
  intro h
  apply selected_not_mem coreCoordinates g hg hp
  rw [← hy,OutsideSelection.U,← SplitParabolic.U_image]
  exact mem_map_of_mem _ h
 have he := congrArg (fun P : Subgroup Unitriangular.T => P.map sylowMap) (core_sup_outside y hu)
 rw [Subgroup.map_sup,MonoidHom.map_zpowers,hy,SplitParabolic.U_image,
  ← MonoidHom.range_eq_map,sylowMap_range] at he
 apply le_antisymm
 · exact sup_le (by rw [OutsideSelection.U,← SplitParabolic.U_image,← sylowMap_range]; exact Unitriangular.U.map_le_range sylowMap)
    (conjugate_le_sylow coreCoordinates g hg)
 · rw [← he]
   exact sup_le_sup_left (zpowers_le.mpr (selected_mem coreCoordinates g)) _

variable {G : Type*} [Group G] (j : Block →* G) (hj : Function.Injective j)

/-- The relative centralizer in the embedded core. -/
def embeddedW : Subgroup G :=
 OutsideSelection.U.map j ⊓ centralizer (OutsideSelection.V2.map j : Set G)

include hj in
theorem W_map : OutsideSelection.W.map j = embeddedW j := by
 ext x
 constructor
 · rintro ⟨w,hw,rfl⟩
   refine ⟨mem_map_of_mem j hw.1,?_⟩
   rintro y ⟨v,hv,rfl⟩
   rw [← map_mul,← map_mul,hw.2 v hv]
 · rintro ⟨⟨w,hw,rfl⟩,hc⟩
   refine ⟨w,⟨hw,?_⟩,rfl⟩
   intro v hv
   apply hj
   simpa only [map_mul] using hc (j v) (mem_map_of_mem j hv)

def embeddedX (g : Block) : Subgroup G :=
 (embeddedW j).map (MulAut.conj (j g)⁻¹).toMonoidHom

include hj in
theorem X_map (g : Block) : (OutsideSelection.X g).map j = embeddedX j g := by
 rw [embeddedX, ← W_map j hj, OutsideSelection.X, Subgroup.map_map, Subgroup.map_map]
 congr 1
 ext w
 simp

noncomputable def coreEquiv : OutsideSelection.U ≃* OutsideSelection.U.map j :=
 OutsideSelection.U.equivMapOfInjective j hj

theorem normalizes_core (x : Block) (hx : x ∈ normalizer (OutsideSelection.U : Set Block)) :
 j x ∈ normalizer (OutsideSelection.U.map j : Set G) :=
 le_normalizer_map j ⟨x,hx,rfl⟩

include hj in
theorem exists_selected_geometry [Finite G] (g : Block) (hg : g ∈ linePreimage) (hp : g ∉ pointPreimage)
 (d : QuaternionCentralProductData (OutsideSelection.U.map j)) :
 ∃ x : G, x ∈ embeddedX j g ∧ x ∉ OutsideSelection.U.map j ∧ x ≠ 1 ∧ x^2=1 ∧
   x ∈ standardSylow.map j ∧
   zpowers x ⊔ ⁅OutsideSelection.U.map j,zpowers x⁆ =
     Stellmacher.elementaryAbelianMaxJ (standardSylow.map j) ∧
   ∃ hn : x ∈ normalizer (OutsideSelection.U.map j : Set G),
     d.IsA2Action ((OutsideSelection.U.map j).normalizerMonoidHom ⟨x,hn⟩) := by
 let e := coreEquiv j hj
 obtain ⟨hgen,hn,ha⟩ := selected_geometry g hg hp (d.map e.symm)
 have hn' := normalizes_core j _ hn
 refine ⟨j (selected g),?_,?_,?_,?_,?_,?_,hn',?_⟩
 · rw [← X_map j hj]
   exact mem_map_of_mem j (selected_mem coreCoordinates g)
 · intro h
   exact selected_not_mem coreCoordinates g hg hp ((mem_map_iff_mem hj).mp h)
 · intro h
   have hs := hj (h.trans j.map_one.symm)
   exact selected_not_mem coreCoordinates g hg hp (hs ▸ OutsideSelection.U.one_mem)
 · rw [← map_pow,selected_square,map_one]
 · exact mem_map_of_mem j (conjugate_le_sylow coreCoordinates g hg (selected_mem coreCoordinates g))
 · rw [← MonoidHom.map_zpowers,← map_commutator,← Subgroup.map_sup,hgen,
     Stellmacher.elementaryAbelianMaxJ_map_injective j hj]
 · apply a2_transport (d.map e.symm) d e _ _ _ ha
   intro u
   apply Subtype.ext
   change j (selected g * (u : Block) * (selected g)⁻¹) =
    j (selected g) * j u * (j (selected g))⁻¹
   simp only [map_mul,map_inv]

end Matrix.PSL3Two.SplitParabolic.SelectedAssembly
