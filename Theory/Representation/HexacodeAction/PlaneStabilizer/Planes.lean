module

public import Theory.Representation.HexacodeAction

/-!
# The six full-weight scalar planes of the hexacode

Evaluation at a coordinate is a binary linear isomorphism on any full-weight
plane: its kernel is zero, and both spaces have dimension two. Thus each such
plane has a unique word whose first coordinate is `a`. The word and its actual
`hexZ` translate generate the plane. In systematic coordinates there are exactly
six such normalized full-weight words, giving a bijection with the actual
subspaces in `IsFullWeightScalarPlane`.

This supplies the six-point set for the stabilizer calculation on printed
p.1155 of Aschbacher–Smith, *The Classification of Quasithin Groups* (combined
manuscript, 1 March 2004). The code, scalar and systematic encoder are the
licensed ATLAS constructions re-exported by `HexacodeAction`.
-/

@[expose] public section

open Atlas.Codes
namespace Representation.Hexacode

/-- The six normalized full-weight words, in systematic coordinates. -/
abbrev PlaneParameters := {t : K × K // hammingNorm (systematicEncoder ![a,t.1,t.2]) = 6}

theorem planeParameters_card : Fintype.card PlaneParameters = 6 := by decide

def planeWord (t : PlaneParameters) : hexacode :=
  ⟨systematicEncoder ![a,t.val.1,t.val.2], systematic_mem _⟩

def scalarEncoder (w : hexacode) : K →ₗ[Bit] hexacode where
  toFun r := r.1 • w + r.2 • action hexZ w
  map_add' := by intros; simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel
  map_smul' := by intros; simp only [Prod.smul_fst, Prod.smul_snd, smul_add,
    smul_smul, smul_eq_mul, RingHom.id_apply]

theorem scalarEncoder_coordinate (w : hexacode) (hw : w.val (hexPos 0) = a) (r : K) :
    (scalarEncoder w r).val (hexPos 0) = r := by
  change r.1 • w.val (hexPos 0) + r.2 • localKappa (w.val (hexPos 0)) = r
  rw [hw]
  revert r
  decide

theorem scalarEncoder_injective (w : hexacode) (hw : w.val (hexPos 0) = a) :
    Function.Injective (scalarEncoder w) := by
  intro r s h
  have he := congrArg (fun v : hexacode => v.val (hexPos 0)) h
  simpa only [scalarEncoder_coordinate w hw] using he

theorem scalarEncoder_rotate (w : hexacode) (r : K) :
    action hexZ (scalarEncoder w r) = scalarEncoder w (r.2, r.1 + r.2) := by
  apply Subtype.ext
  funext i
  change (if i.2 = 0 then localKappa else localKappa⁻¹)
    (r.1 • w.val i + r.2 • (if i.2 = 0 then localKappa else localKappa⁻¹) (w.val i)) =
    r.2 • w.val i + (r.1 + r.2) • (if i.2 = 0 then localKappa else localKappa⁻¹) (w.val i)
  generalize w.val i = u
  revert i r u
  decide

theorem scalarEncoder_weight (w : hexacode) (r : K) (hr : r ≠ 0) :
    hammingNorm (scalarEncoder w r : HexWord) = hammingNorm (w : HexWord) := by
  have hc : ∀ (r : K), r ≠ 0 → ∀ (i : HexIndex) (u : K),
      (r.1 • u + r.2 • (if i.2 = 0 then localKappa else localKappa⁻¹) u = 0 ↔ u = 0) := by decide
  unfold hammingNorm
  congr 1
  apply Finset.filter_congr
  intro i _
  exact not_congr (hc r hr i (w.val i))

def scalarPlane (w : hexacode) : Submodule Bit hexacode := (scalarEncoder w).range

theorem scalarPlane_stable (w : hexacode) :
    hexZ ∈ BinaryOffender.subspaceStabilizer action (scalarPlane w) := by
  intro v
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨(r.1 + r.2, r.1), ?_⟩
    apply (hexAction hexZ).injective
    change action hexZ (scalarEncoder w (r.1 + r.2, r.1)) = action hexZ v
    rw [scalarEncoder_rotate]
    have he : r.1 + r.2 + r.1 = r.2 := by rw [add_right_comm, bit_self_add, zero_add]
    rw [he]
    exact hr
  · rintro ⟨r, rfl⟩
    exact ⟨(r.2, r.1 + r.2), (scalarEncoder_rotate w r).symm⟩

theorem scalarPlane_finrank (w : hexacode) (hw : w.val (hexPos 0) = a) :
    Module.finrank Bit (scalarPlane w) = 2 := by
  rw [scalarPlane, LinearMap.finrank_range_of_inj (scalarEncoder_injective w hw)]
  simp [K, Letter, Module.finrank_prod]

theorem scalarPlane_full (w : hexacode) (hw : w.val (hexPos 0) = a)
    (hn : hammingNorm w.val = 6) : IsFullWeightScalarPlane (scalarPlane w) := by
  refine ⟨scalarPlane_finrank w hw, scalarPlane_stable w, ?_⟩
  rintro ⟨v, r, rfl⟩ hv
  have hr : r ≠ 0 := by
    intro h
    apply hv
    apply Subtype.ext
    change scalarEncoder w r = 0
    rw [h, map_zero]
  exact (scalarEncoder_weight w r hr).trans hn

def parameterPlane (t : PlaneParameters) :
    {P : Submodule Bit hexacode // IsFullWeightScalarPlane P} :=
  ⟨scalarPlane (planeWord t), scalarPlane_full _ rfl t.property⟩

theorem scalarPlane_word (w : hexacode) : w ∈ scalarPlane w := by
  refine ⟨a, ?_⟩
  change (1 : Bit) • w + (0 : Bit) • action hexZ w = w
  simp

theorem parameterPlane_injective : Function.Injective parameterPlane := by
  intro t s he
  have hm := scalarPlane_word (planeWord t)
  rw [show scalarPlane (planeWord t) = scalarPlane (planeWord s) from congrArg Subtype.val he] at hm
  obtain ⟨r,hr⟩ := hm
  have hc := congrArg (fun w : hexacode => w.val (hexPos 0)) hr
  rw [scalarEncoder_coordinate _ rfl] at hc
  change r = a at hc
  subst r
  have hword : planeWord s = planeWord t := by
    simpa [scalarEncoder, a] using hr
  apply Subtype.ext
  apply Prod.ext
  · exact (congrArg (fun w : hexacode => w.val (hexPos 1)) hword).symm
  · exact (congrArg (fun w : hexacode => w.val (hexPos 2)) hword).symm

theorem full_weight_coordinate_ne_zero (w : HexWord) (hw : hammingNorm w = 6)
    (i : HexIndex) : w i ≠ 0 := by
  have hc : (Finset.univ.filter (fun j => w j ≠ 0)).card =
      (Finset.univ : Finset HexIndex).card := hw
  exact Finset.card_filter_eq_iff.mp hc i (Finset.mem_univ _)

theorem plane_coordinate_bijective (P : Submodule Bit hexacode)
    (hP : IsFullWeightScalarPlane P) :
    Function.Bijective ((hexCoordinate (hexPos 0)).comp P.subtype) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro w hw
    change w = 0
    by_contra hn
    exact full_weight_coordinate_ne_zero w.val.val (hP.2.2 w hn) (hexPos 0) hw
  · rw [Module.natCard_eq_pow_finrank (K := Bit), hP.1]
    norm_num [Nat.card_eq_fintype_card, K, Letter, ZMod.card]

theorem scalarPlane_eq_of_mem (P : Submodule Bit hexacode)
    (hP : IsFullWeightScalarPlane P) (w : hexacode) (hw : w ∈ P)
    (ha : w.val (hexPos 0) = a) : scalarPlane w = P := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨r,rfl⟩
    exact P.add_mem (P.smul_mem _ hw) (P.smul_mem _ ((hP.2.1 w).2 hw))
  · rw [scalarPlane_finrank w ha, hP.1]

theorem parameterPlane_surjective : Function.Surjective parameterPlane := by
  rintro ⟨P,hP⟩
  obtain ⟨w,hw⟩ := (plane_coordinate_bijective P hP).2 a
  have ha : w.val.val (hexPos 0) = a := hw
  have hn : w ≠ 0 := by
    intro he
    have hh : (0 : K) = a := by simpa [he] using ha
    exact (by decide : (0 : K) ≠ a) hh
  have he : systematicEncoder ![a,w.val.val (hexPos 1),w.val.val (hexPos 2)] = w.val.val := by
    rw [← systematic_reconstruct w.val]
    apply congrArg systematicEncoder
    funext i
    fin_cases i
    · exact ha.symm
    · rfl
    · rfl
  let t : PlaneParameters := ⟨(w.val.val (hexPos 1), w.val.val (hexPos 2)), by
    rw [he]
    exact hP.2.2 w hn⟩
  refine ⟨t, ?_⟩
  apply Subtype.ext
  have ht : planeWord t = w.val := Subtype.ext he
  change scalarPlane (planeWord t) = P
  rw [ht]
  exact scalarPlane_eq_of_mem P hP w.val w.property ha

/-- The actual subspaces, not a separate family label. -/
abbrev FullWeightScalarPlane := {P : Submodule Bit hexacode // IsFullWeightScalarPlane P}

noncomputable def planeParametersEquiv : PlaneParameters ≃ FullWeightScalarPlane :=
  Equiv.ofBijective parameterPlane ⟨parameterPlane_injective, parameterPlane_surjective⟩

noncomputable instance : Fintype FullWeightScalarPlane :=
  Fintype.ofEquiv PlaneParameters planeParametersEquiv

theorem fullWeightScalarPlane_card : Fintype.card FullWeightScalarPlane = 6 := by
  exact (Fintype.card_congr planeParametersEquiv).symm.trans planeParameters_card

end Representation.Hexacode
