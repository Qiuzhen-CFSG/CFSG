module

public import Stellmacher.Recognition.Parrott.NormalizerRootCosetCounts
public import Stellmacher.Recognition.Parrott.NormalizerRootDiscrepancyCorrection
public import Stellmacher.Recognition.Parrott.NormalizerRootExhaustion

/-!
# Root census and transport correction in Parrott's normalizer

Multiplying a supplied transport involution by vt preserves its transport
fields: the transport fixes vt, and vt centralizes the prescribed y-image.
Conjugation by vt multiplies caw by z. Consequently a root-image discrepancy
in the central four-group ⟨t,z⟩ can be corrected to either 1 or tz without
changing the supplied centralizer frame.

The imported discrepancy correction first removes the u-coordinate by an
involutory twist s(ab). Composing the two corrections gives the required
x-image alternatives from the supplied local-coordinate premises, retaining
the literal centralizer frame and every transport field.

The general sixteen-root census, with eight roots in each elementary coset,
is re-exported from `NormalizerRootExhaustion`. The transport correction uses
the explicit twists and does not require an involution-orbit equality.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.682, the paragraph selecting the image of x.
-/

open Subgroup
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
variable {f : ParrottCentralizerGeneratorData n}
private theorem tail {a b c : G} (h : a * b = c) (d : G) :
    a * (b * d) = c * d := by rw [← mul_assoc, h]
private theorem inv_of_sq {g : G} (h : g ^ 2 = 1) : g⁻¹ = g :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h)

private theorem fixed_vt (k : ParrottNormalizerTransportData f) :
    Commute k.s (n.v * n.t) := by
  have he : k.s⁻¹ * (n.v * n.t) * k.s = n.v * n.t := by
    calc
      _ = (k.s⁻¹ * n.v * k.s) * (k.s⁻¹ * n.t * k.s) := by group
      _ = _ := by rw [k.v_conj, k.t_conj]; simp only [mul_assoc, ← pow_two, f.z_sq, mul_one]
  change k.s * (n.v * n.t) = (n.v * n.t) * k.s
  calc
    _ = k.s * (k.s⁻¹ * (n.v * n.t) * k.s) := by rw [he]
    _ = _ := by group

set_option linter.unusedSimpArgs false in
private theorem vt_conj_caw :
    (n.v * n.t)⁻¹ * (f.c * f.a * f.w) * (n.v * n.t) = f.c * f.a * f.w * z := by
  have cv := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq10_cv
  have vc : n.v * f.c = f.c * n.v * z := by rw [cv]; simp only [mul_assoc, ← pow_two, f.z_sq, mul_one]
  have tc := ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq10_ct).symm.eq
  have vv : n.v * n.v = 1 := by simpa only [pow_two] using f.v_sq
  have tt : n.t * n.t = 1 := by simpa only [pow_two] using f.t_sq
  simp only [mul_inv_rev, inv_of_sq f.t_sq, inv_of_sq f.v_sq, mul_assoc,
    tail vc, tail tc, tail f.comm_zv.eq, tail f.comm_zt.eq,
    tail f.comm_az.symm.eq, tail f.comm_at.symm.eq, tail f.comm_av.symm.eq,
    tail f.comm_tw.eq, tail f.comm_vw.eq, tail f.comm_zw.eq,
    tail f.comm_tv.eq, f.comm_zt.eq, tail vv, tail tt, tt, one_mul, mul_one]

/-- Twist the transport by its fixed involution vt, retaining the same frame. -/
public def ParrottNormalizerTransportData.twistVT (k : ParrottNormalizerTransportData f) :
    ParrottNormalizerTransportData f where
  s := k.s * (n.v * n.t)
  mem_normalizer := (normalizer (e.F : Set G)).mul_mem k.mem_normalizer
    (le_normalizer (e.F.mul_mem n.v_mem_inf.2 n.t_mem_inf.2))
  sq := by
    rw [(fixed_vt k).mul_pow, k.sq, f.comm_tv.symm.mul_pow, f.v_sq, f.t_sq]
    simp
  t_conj := by
    calc
      _ = (n.v * n.t)⁻¹ * (k.s⁻¹ * n.t * k.s) * (n.v * n.t) := by group
      _ = z := by
        rw [k.t_conj, (f.comm_zv.mul_right f.comm_zt).inv_right.symm.eq]
        group
  v_conj := by
    have hc : Commute (n.v * n.t * z) (n.v * n.t) :=
      (Commute.refl _).mul_left (f.comm_zv.mul_right f.comm_zt)
    calc
      _ = (n.v * n.t)⁻¹ * (k.s⁻¹ * n.v * k.s) * (n.v * n.t) := by group
      _ = _ := by rw [k.v_conj, hc.inv_right.symm.eq]; group
  y_conj := by
    have hc : Commute (f.w * f.u * n.v * z) (n.v * n.t) :=
      (((f.comm_vw.symm.mul_left f.comm_vu.symm).mul_left (Commute.refl _)).mul_left
        f.comm_zv).mul_right
      (((f.comm_tw.symm.mul_left f.comm_tu.symm).mul_left f.comm_tv.symm).mul_left
        f.comm_zt)
    calc
      _ = (n.v * n.t)⁻¹ * (k.s⁻¹ * f.y * k.s) * (n.v * n.t) := by group
      _ = _ := by rw [k.y_conj, hc.inv_right.symm.eq]; group

/-- The correcting transporter is the literal product s(vt). -/
public theorem ParrottNormalizerTransportData.twistVT_s (k : ParrottNormalizerTransportData f) :
    k.twistVT.s = k.s * (n.v * n.t) := by rfl

/-- The fixed twist toggles z in a root image whose discrepancy commutes with vt. -/
public theorem ParrottNormalizerTransportData.twistVT_x (k : ParrottNormalizerTransportData f)
    (d : G) (hd : Commute d (n.v * n.t))
    (hx : k.s⁻¹ * f.x * k.s = f.c * f.a * f.w * d) :
    k.twistVT.s⁻¹ * f.x * k.twistVT.s = f.c * f.a * f.w * z * d := by
  rw [k.twistVT_s]
  calc
    _ = (n.v * n.t)⁻¹ * (k.s⁻¹ * f.x * k.s) * (n.v * n.t) := by group
    _ = ((n.v * n.t)⁻¹ * (f.c * f.a * f.w) * (n.v * n.t)) * d := by
      rw [hx, mul_assoc, mul_assoc, hd.eq]; group
    _ = _ := by rw [vt_conj_caw]
end Stellmacher.Recognition
namespace Stellmacher.Recognition
open Subgroup
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
variable {f : ParrottCentralizerGeneratorData n}

/-- Four central root images reduce to the two required representatives. -/
public theorem ParrottNormalizerTransportData.exists_corrected_of_four_images
    (k : ParrottNormalizerTransportData f)
    (hx : k.s⁻¹ * f.x * k.s = f.c * f.a * f.w ∨
      k.s⁻¹ * f.x * k.s = f.c * f.a * f.w * z ∨
      k.s⁻¹ * f.x * k.s = f.c * f.a * f.w * n.t ∨
      k.s⁻¹ * f.x * k.s = f.c * f.a * f.w * n.t * z) :
    ∃ k' : ParrottNormalizerTransportData f,
      k'.s⁻¹ * f.x * k'.s = f.c * f.a * f.w ∨
      k'.s⁻¹ * f.x * k'.s = f.c * f.a * f.w * n.t * z := by
  rcases hx with hx | hx | hx | hx
  · exact ⟨k, Or.inl hx⟩
  · refine ⟨k.twistVT, Or.inl ?_⟩
    have hh := k.twistVT_x z (f.comm_zv.mul_right f.comm_zt) hx
    simpa only [mul_assoc, ← pow_two, f.z_sq, mul_one] using hh
  · refine ⟨k.twistVT, Or.inr ?_⟩
    have hh := k.twistVT_x n.t (f.comm_tv.mul_right (Commute.refl _)) hx
    simpa only [mul_assoc, f.comm_zt.eq] using hh
  · exact ⟨k, Or.inr hx⟩

/-- A discrepancy in the central four-group can be removed up to tz. -/
public theorem ParrottNormalizerTransportData.exists_corrected_of_central_discrepancy
    (k : ParrottNormalizerTransportData f)
    (hx : (f.c * f.a * f.w)⁻¹ * (k.s⁻¹ * f.x * k.s) ∈
      closure ({n.t, z} : Set G)) :
    ∃ k' : ParrottNormalizerTransportData f,
      k'.s⁻¹ * f.x * k'.s = f.c * f.a * f.w ∨
      k'.s⁻¹ * f.x * k'.s = f.c * f.a * f.w * n.t * z := by
  apply k.exists_corrected_of_four_images
  have he := (mem_closure_pair_iff n.t z
    (by simpa only [pow_two] using f.t_sq)
    (by simpa only [pow_two] using f.z_sq) f.comm_zt.symm _).mp hx
  rcases he with he | he | he | he
  · exact Or.inl (by simpa only [mul_one] using inv_mul_eq_iff_eq_mul.mp he)
  · exact Or.inr (Or.inr (Or.inl (inv_mul_eq_iff_eq_mul.mp he)))
  · exact Or.inr (Or.inl (inv_mul_eq_iff_eq_mul.mp he))
  · exact Or.inr (Or.inr (Or.inr (by
      simpa only [← mul_assoc] using inv_mul_eq_iff_eq_mul.mp he)))

/-- Correct the transported root from its local coordinates, preserving the
supplied frame and all transport fields. The first twist removes u from the
discrepancy; the fixed involution vt then removes z up to the representative tz. -/
public theorem ParrottNormalizerTransportData.exists_corrected_of_local_coordinates
    [Finite G] (k : ParrottNormalizerTransportData f)
    (ha : k.s⁻¹ * f.a * k.s = f.u ∨ k.s⁻¹ * f.a * k.s = f.u * z)
    (hx : (f.c * f.a * f.w)⁻¹ * (k.s⁻¹ * f.x * k.s) ∈
      closure ({f.u, n.t, z} : Set G)) :
    ∃ k' : ParrottNormalizerTransportData f,
      k'.s⁻¹ * f.x * k'.s = f.c * f.a * f.w ∨
      k'.s⁻¹ * f.x * k'.s = f.c * f.a * f.w * n.t * z := by
  obtain ⟨k0, hk0⟩ := k.exists_corrected_of_u_discrepancy ha hx
  exact k0.exists_corrected_of_central_discrepancy hk0
end Stellmacher.Recognition
