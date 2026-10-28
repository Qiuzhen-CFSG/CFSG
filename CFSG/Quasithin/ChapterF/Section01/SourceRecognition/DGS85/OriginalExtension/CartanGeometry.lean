module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.ApartmentAction
public import Theory.GroupTheory.WeakBNPair.RegularTree.ApartmentSeparation

/-!
# Original apartment preservation from local Cartan geometry

A Cartan-fixed subtree cannot leave a two-sided apartment if no vertex of
its fixed subtree has three fixed neighbors. Uniqueness of the apartment
through the chosen long path first makes its reduced pointwise stabilizer
fix the entire apartment. Reduced path transitivity then aligns an original
semilinear actor with a reduced translator on that path; their transports
of the actual Cartan subgroup agree. The fixed-set calculation consequently
makes the actor preserve the reduced apartment family and hence its quotient
kernel.

This proves the regular no-branching case of the geometric extension step
in Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985), (15.2),
printed p.227. The local fixed-neighbor calculation remains an explicit
input: the small-field obstruction cases on pp.227--228 must not be discarded.
No original apartment preservation, Cartan conjugacy, completion kernel
invariance, or classification conclusion is assumed.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.WeakBNPair.RegularTree
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.CartanGeometry
variable {Y V : Type*} [Group Y] [MulAction Y V]
  {Γ : SimpleGraph V} {T : Set V}

private theorem fixed_path (htree : Γ.IsTree)
    (hact : ∀ (g : Y) {v w : V}, Γ.Adj v w → Γ.Adj (g • v) (g • w))
    (C : Subgroup Y) {v w : V} (p : Γ.Walk v w) (hp : p.IsPath)
    (hv : ∀ g ∈ C, g • v = v) (hw : ∀ g ∈ C, g • w = w) :
    ∀ z ∈ p.support, ∀ g ∈ C, g • z = z := by
  intro z hz g hg
  let f : Γ →g Γ := ⟨(g • ·), hact g⟩
  let q : Γ.Walk v w := (p.map f).copy (hv g hg) (hw g hg)
  have hq : q.IsPath := (isPath_copy ..).mpr (hp.map (MulAction.toPerm g).injective)
  have he : q = p := congrArg Subtype.val
    ((htree.isAcyclic.subsingleton_path v w).elim ⟨q,hq⟩ ⟨p,hp⟩)
  obtain ⟨i,hi,_⟩ := mem_support_iff_exists_getVert.mp hz
  have hh := congrArg (fun r : Γ.Walk v w => r.getVert i) he
  simpa [q, f, hi] using hh

/-- Local absence of a third Cartan-fixed neighbor identifies the whole fixed
subtree. In particular this proves the global fixed-set premise used in descent. -/
theorem fixed_set_of_local_degree (htree : Γ.IsTree)
    (hact : ∀ (g : Y) {v w : V}, Γ.Adj v w → Γ.Adj (g • v) (g • w))
    (C : Subgroup Y) (hne : T.Nonempty) (hdeg : TwoNeighborsIn Γ T)
    (hfix : ∀ v ∈ T, ∀ g ∈ C, g • v = v)
    (hthin : NoBranchingIn Γ {v | ∀ g ∈ C, g • v = v}) :
    ∀ v, v ∈ T ↔ ∀ g ∈ C, g • v = v := by
  have hclosed : ∀ {v w}, v ∈ T → Γ.Adj v w → (∀ g ∈ C, g • w = w) → w ∈ T := by
    intro v w hv hvw hw
    obtain ⟨b,hb,c,hc,hvb,hvc,hbc⟩ := hdeg v hv
    rcases hthin v (hfix v hv) b (hfix b hb) c (hfix c hc) w hw
      hvb hvc hvw hbc with he | he
    · exact he ▸ hb
    · exact he ▸ hc
  intro w
  refine ⟨hfix w, ?_⟩
  intro hw
  obtain ⟨v,hv⟩ := hne
  obtain ⟨p,hp,_⟩ := htree.connected.exists_path_of_dist v w
  have hpf := fixed_path htree hact C p hp (hfix v hv) hw
  have hall : ∀ {a b} (q : Γ.Walk a b), a ∈ T →
      (∀ z ∈ q.support, ∀ g ∈ C, g • z = z) → b ∈ T := by
    intro a b q
    induction q with
    | nil => exact fun ha _ => ha
    | @cons a b c hab q ih =>
      intro ha hq
      exact ih (hclosed ha hab (hq b (by simp)))
        (fun z hz => hq z (by simp only [support_cons, List.mem_cons]; exact Or.inr hz))
  exact hall p hv hpf

/-- A semilinear actor and a reduced translator agreeing along a path induce
the same transport of its actual pointwise stabilizer. -/
theorem cartan_conjugate_of_path_alignment
    (e : MulAut Y) (f : Γ ≃g Γ)
    (heq : ∀ g v, f (g • v) = e g • f v)
    {a b : V} (p : Γ.Walk a b) (C : Subgroup Y)
    (hC : ∀ g, g ∈ C ↔ ∀ k ≤ p.length, g • p.getVert k = p.getVert k)
    (t : Y) (halign : ∀ k ≤ p.length, t • p.getVert k = f (p.getVert k)) :
    C.map e.toMonoidHom = C.map (MulAut.conj t).toMonoidHom := by
  have hmem (g : Y) : e g ∈ C.map (MulAut.conj t).toMonoidHom ↔ g ∈ C := by
    constructor
    · rintro ⟨x,hx,hxg⟩
      apply (hC g).mpr
      intro k hk
      apply f.injective
      rw [heq, ← halign k hk]
      change t*x*t⁻¹ = e g at hxg
      rw [← hxg, mul_smul, mul_smul, inv_smul_smul, (hC x).mp hx k hk]
    · intro hg
      refine ⟨t⁻¹ * e g * t, (hC _).mpr ?_, ?_⟩
      · intro k hk
        rw [mul_smul, mul_smul, halign k hk, ← heq, (hC g).mp hg k hk,
          ← halign k hk, inv_smul_smul]
      · change t * (t⁻¹ * e g * t) * t⁻¹ = e g
        simp [mul_assoc]
  ext x
  obtain ⟨g,rfl⟩ := e.surjective x
  constructor
  · rintro ⟨k,hk,he⟩
    have hkg : k = g := e.injective he
    have hg : g ∈ C := hkg ▸ hk
    exact (hmem g).mpr hg
  · intro hx
    have hg : g ∈ C := (hmem g).mp hx
    exact ⟨g,hg,rfl⟩

/-- Reduced path transitivity supplies the aligning element; no conjugacy of
Cartans under the original outer actor is assumed. -/
theorem cartan_conjugate_of_path_transitivity
    (e : MulAut Y) (f : Γ ≃g Γ)
    (heq : ∀ g v, f (g • v) = e g • f v)
    {s : ℕ} (htrans : BasedPathTransitive (X := Y) Γ s)
    {a b : V} (p : Γ.Walk a b) (hp : p.IsPath) (hlen : p.length = s)
    (hbase : f a = a) (C : Subgroup Y)
    (hC : ∀ g, g ∈ C ↔ ∀ k ≤ p.length, g • p.getVert k = p.getVert k) :
    ∃ t : Y, C.map e.toMonoidHom = C.map (MulAut.conj t).toMonoidHom := by
  let q : Γ.Walk a (f b) := (p.map f.toHom).copy hbase rfl
  have hq : q.IsPath := (isPath_copy ..).mpr (hp.map f.injective)
  have hqlen : q.length = s := by simpa only [q, length_copy, length_map] using hlen
  obtain ⟨t,ht⟩ := htrans p q hp hq hlen hqlen
  refine ⟨t, cartan_conjugate_of_path_alignment e f heq p C hC t ?_⟩
  intro k hk
  simpa [q, hlen] using ht k (hlen ▸ hk)

private theorem fixes_line_of_fixed_edge
    (hline : NoBranchingIn Γ T) (hconn : (Γ.induce T).Preconnected)
    (f : Γ ≃g Γ) (hfT : ∀ v ∈ T, f v ∈ T)
    {a b : V} (ha : a ∈ T) (hb : b ∈ T) (hab : Γ.Adj a b)
    (hfa : f a = a) (hfb : f b = b) : ∀ v ∈ T, f v = v := by
  have hnext : ∀ {v w z}, v ∈ T → w ∈ T → z ∈ T →
      Γ.Adj v w → Γ.Adj v z → f v = v → f w = w → f z = z := by
    intro v w z hv hw hz hvw hvz hfv hfw
    by_cases hwz : w = z
    · exact hwz ▸ hfw
    have hvfz : Γ.Adj v (f z) := by
      have hh := f.toHom.map_adj hvz
      change Γ.Adj (f v) (f z) at hh
      simpa only [hfv] using hh
    rcases hline v hv w hw z hz (f z) (hfT z hz) hvw hvz hvfz hwz with he | he
    · exact (hwz (f.injective (hfw.trans he.symm))).elim
    · exact he
  have hwalk : ∀ {v w : T} (q : (Γ.induce T).Walk v w),
      f v = v → (∃ z ∈ T, Γ.Adj v z ∧ f z = z) → f w = w := by
    intro v w q
    induction q with
    | nil => exact fun hv _ => hv
    | @cons v w z hvw q ih =>
      intro hfv ⟨u,hu,hvu,hfu⟩
      have hfw : f w = w := hnext v.property hu w.property hvu hvw hfv hfu
      exact ih hfw ⟨v,v.property,hvw.symm,hfv⟩
  intro v hv
  obtain ⟨q⟩ := hconn ⟨a,ha⟩ ⟨v,hv⟩
  exact hwalk q hfa ⟨b,hb,hab,hfb⟩

/-- Uniqueness of the apartment containing the marked path makes its reduced
pointwise stabilizer fix the entire apartment, not merely preserve it as a set. -/
theorem cartan_fixes_apartment_of_uniqueness
    (hact : ∀ (g : Y) {v w : V}, Γ.Adj v w → Γ.Adj (g • v) (g • w))
    (hline : NoBranchingIn Γ T) (hconn : (Γ.induce T).Preconnected)
    {s : ℕ} (hs : 0 < s) (hunique : ApartmentsUnique (X := Y) Γ T s)
    {a b : V} (p : Γ.Walk a b) (hp : p.IsPath) (hlen : p.length = s)
    (hpT : ∀ v ∈ p.support, v ∈ T) (C : Subgroup Y)
    (hC : ∀ g, g ∈ C ↔ ∀ k ≤ p.length, g • p.getVert k = p.getVert k) :
    ∀ v ∈ T, ∀ g ∈ C, g • v = v := by
  intro v hv g hg
  have hgfix := (hC g).mp hg
  have hgpath : ∀ z ∈ p.support, g • z = z := by
    intro z hz
    obtain ⟨k,hk,hkl⟩ := mem_support_iff_exists_getVert.mp hz
    simpa only [hk] using hgfix k hkl
  have hA := hunique p hp hlen 1 g
    (fun z hz => ⟨z,hpT z hz,one_smul Y z⟩)
    (fun z hz => ⟨z,hpT z hz,hgpath z hz⟩)
  have hgT : ∀ z ∈ T, g • z ∈ T := by
    intro z hz
    have : g • z ∈ apartmentTranslate T (1 : Y) := hA ▸ ⟨z,hz,rfl⟩
    obtain ⟨w,hw,he⟩ := this
    have he' : g • z = w := by simpa only [one_smul] using he.symm
    rw [he']
    exact hw
  let f : Γ ≃g Γ := {
    toEquiv := MulAction.toPerm g
    map_rel_iff' := by
      intro x y
      change Γ.Adj (g • x) (g • y) ↔ Γ.Adj x y
      constructor
      · intro h
        simpa only [inv_smul_smul] using hact g⁻¹ h
      · exact hact g }
  have hpos : 0 < p.length := by omega
  apply fixes_line_of_fixed_edge hline hconn f hgT
    (hpT a p.start_mem_support) (hpT _ (p.getVert_mem_support 1))
    (by simpa only [getVert_zero] using p.adj_getVert_succ hpos)
    (hgpath a p.start_mem_support) (hgfix 1 (by omega)) v hv

/-- The local Cartan fixed-neighbor condition and reduced path transitivity
force preservation of the apartment by an original actor fixing its base. -/
theorem apartment_image_of_local_cartan
    (htree : Γ.IsTree)
    (hact : ∀ (g : Y) {v w : V}, Γ.Adj v w → Γ.Adj (g • v) (g • w))
    (C : Subgroup Y) (hne : T.Nonempty) (hdeg : TwoNeighborsIn Γ T)
    (hfix : ∀ v ∈ T, ∀ g ∈ C, g • v = v)
    (hthin : NoBranchingIn Γ {v | ∀ g ∈ C, g • v = v})
    (e : MulAut Y) (f : Γ ≃g Γ)
    (heq : ∀ g v, f (g • v) = e g • f v)
    {s : ℕ} (htrans : BasedPathTransitive (X := Y) Γ s)
    {a b : V} (p : Γ.Walk a b) (hp : p.IsPath) (hlen : p.length = s)
    (hbase : f a = a)
    (hC : ∀ g, g ∈ C ↔ ∀ k ≤ p.length, g • p.getVert k = p.getVert k) :
    ∃ t : Y, ∀ v ∈ T, ∃ w ∈ T, f v = t • w := by
  obtain ⟨t,ht⟩ := cartan_conjugate_of_path_transitivity e f heq htrans p hp hlen hbase C hC
  exact ⟨t, ApartmentAction.apartment_image_of_cartan e f heq C
    (fixed_set_of_local_degree htree hact C hne hdeg hfix hthin) t ht⟩

/-- The regular source route outside the local branching obstructions: reduced
path uniqueness and transitivity, together with the fixed-neighbor calculation,
supply the original apartment-preservation conclusion. -/
theorem apartment_image_of_thin_path_stabilizer
    (htree : Γ.IsTree)
    (hact : ∀ (g : Y) {v w : V}, Γ.Adj v w → Γ.Adj (g • v) (g • w))
    (hdeg : TwoNeighborsIn Γ T) (hline : NoBranchingIn Γ T)
    (hconn : (Γ.induce T).Preconnected)
    {s : ℕ} (hs : 0 < s) (hunique : ApartmentsUnique (X := Y) Γ T s)
    (htrans : BasedPathTransitive (X := Y) Γ s)
    {a b : V} (p : Γ.Walk a b) (hp : p.IsPath) (hlen : p.length = s)
    (hpT : ∀ v ∈ p.support, v ∈ T) (C : Subgroup Y)
    (hC : ∀ g, g ∈ C ↔ ∀ k ≤ p.length, g • p.getVert k = p.getVert k)
    (hthin : NoBranchingIn Γ {v | ∀ g ∈ C, g • v = v})
    (e : MulAut Y) (f : Γ ≃g Γ)
    (heq : ∀ g v, f (g • v) = e g • f v) (hbase : f a = a) :
    ∃ t : Y, ∀ v ∈ T, ∃ w ∈ T, f v = t • w :=
  apartment_image_of_local_cartan htree hact C ⟨a,hpT a p.start_mem_support⟩ hdeg
    (cartan_fixes_apartment_of_uniqueness hact hline hconn hs hunique p hp hlen hpT C hC)
    hthin e f heq htrans p hp hlen hbase hC

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.CartanGeometry
