module

public import CFSG.Quasithin.ChapterJ.Section01To02.Preliminaries
public import Theory.Representation.PSL3Two.NaturalOrbits

/-!
# Fusion of the elementary subgroup U

J.2.1 supplies |Z| = 2 and Z ≤ V. Ru2 then moves an element of U outside Z
to the coset of an element of V outside Z. Its actual conjugate lies in V,
because the coordinate kernel Z lies in V. The natural Ru1 action moves
this nonidentity element to any chosen nonidentity z in Z.

The proof constructs conjugators in H and L before composing them in G;
no fusion or ambient recognition assertion is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.6(4), printed p.434 (PDF p.445 of `refs/quasithin.pdf`).
-/

public section
noncomputable section
open Subgroup Representation

namespace CFSG.Quasithin.ChapterJ
variable {G : Type*} [Group G]

/-- The actual L-conjugation action is transitive on V minus the identity. -/
theorem RuOne.conjugate_nonidentity {L V : Subgroup G} (r : RuOne L V)
    {v w : G} (hv : v ∈ V) (hw : w ∈ V) (hv1 : v ≠ 1) (hw1 : w ≠ 1) :
    ∃ l : L, (l : G) * v * (l : G)⁻¹ = w := by
  have hinj : Function.Injective r.natural.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [r.natural.kernel_eq, bot_subgroupOf]
  have hv0 : (r.natural.coordinates ⟨v, hv⟩).toAdd ≠ 0 := by
    intro h
    exact hv1 ((Subgroup.mem_bot.mp ((r.natural.coordinates_eq_one_iff _).mp h)))
  have hw0 : (r.natural.coordinates ⟨w, hw⟩).toAdd ≠ 0 := by
    intro h
    exact hw1 ((Subgroup.mem_bot.mp ((r.natural.coordinates_eq_one_iff _).mp h)))
  obtain ⟨g, hg⟩ := BinaryLinearThree.natural_transitive_nonzero _ _ hv0 hw0
  obtain ⟨l, hl⟩ := r.quotient_surjective g
  refine ⟨l, ?_⟩
  let c : V := ⟨(l : G) * v * (l : G)⁻¹,
    (mem_normalizer_iff.mp (r.natural.normalized l.property) v).mp hv⟩
  change (c : G) = ((⟨w, hw⟩ : V) : G)
  apply congrArg (fun a : V => (a : G))
  apply hinj
  apply Multiplicative.toAdd.injective
  calc
    _ = BinaryLinearThree.W (r.quotientMap l)
        (r.natural.coordinates ⟨v, hv⟩).toAdd := r.natural.equivariant l ⟨v, hv⟩
    _ = _ := by rw [hl]; exact hg

variable [Finite G]

/-- H moves every element of U into V, using the actual coordinates on U/Z. -/
theorem TypeRuSetup.conjugate_U_into_V (d : TypeRuSetup G)
    (hZ : Nat.card d.Z = 2) (hZV : d.Z ≤ d.V)
    {u : G} (hu : u ∈ d.U) :
    ∃ h : d.H, (h : G) * u * (h : G)⁻¹ ∈ d.V := by
  by_cases huZ : u ∈ d.Z
  · exact ⟨1, by simpa using hZV huZ⟩
  have hVU : d.V ≤ d.U := le_conjugateSpan d.H d.V
  have hseed : ∃ v : d.V, (v : G) ∉ d.Z := by
    by_contra! hn
    have hle : d.V ≤ d.Z := fun v hv => hn ⟨v, hv⟩
    have hc := card_le_of_le hle
    rw [d.ru1.card_V, hZ] at hc
    omega
  obtain ⟨v, hv⟩ := hseed
  let vU : d.U := ⟨v, hVU v.property⟩
  let uU : d.U := ⟨u, hu⟩
  have hv0 : (d.ru2.natural.coordinates vU).toAdd ≠ 0 := by
    intro h
    exact hv ((d.ru2.natural.coordinates_eq_one_iff _).mp h)
  have hu0 : (d.ru2.natural.coordinates uU).toAdd ≠ 0 := by
    intro h
    exact huZ ((d.ru2.natural.coordinates_eq_one_iff _).mp h)
  obtain ⟨h, hh⟩ := d.ru2.transitive_natural _ _ hu0 hv0
  let c : d.U := ⟨h * u * (h : G)⁻¹,
    (mem_normalizer_iff.mp (d.ru2.natural.normalized h.property) u).mp hu⟩
  have hc : d.ru2.natural.coordinates c = d.ru2.natural.coordinates vU :=
    Multiplicative.toAdd.injective ((d.ru2.natural.equivariant h uU).trans hh)
  have hcZ : ((c * vU⁻¹ : d.U) : G) ∈ d.Z := by
    apply (d.ru2.natural.coordinates_eq_one_iff _).mp
    rw [map_mul, map_inv, hc, mul_inv_cancel]
  refine ⟨h, ?_⟩
  have hm := d.V.mul_mem (hZV hcZ) v.property
  simpa [c, vU, mul_assoc] using hm

/-- The U-fusion assertion of J.2.6(4), conditional only on the two earlier
J.2.1 conclusions about Z. -/
theorem TypeRuSetup.fusion_U (d : TypeRuSetup G)
    (hZ : Nat.card d.Z = 2) (hZV : d.Z ≤ d.V)
    {z : G} (hz : z ∈ d.Z) (hz1 : z ≠ 1)
    {u : G} (hu : u ∈ d.U) (hu1 : u ≠ 1) : IsConj u z := by
  obtain ⟨h, hh⟩ := d.conjugate_U_into_V hZ hZV hu
  have hn : (h : G) * u * (h : G)⁻¹ ≠ 1 := by
    intro he
    apply hu1
    apply (MulAut.conj (h : G)).injective
    rw [map_one, MulAut.conj_apply]
    exact he
  obtain ⟨l, hl⟩ := d.ru1.conjugate_nonidentity hh (hZV hz) hn hz1
  exact (isConj_iff.mpr ⟨(h : G), rfl⟩).trans (isConj_iff.mpr ⟨(l : G), hl⟩)
end CFSG.Quasithin.ChapterJ
