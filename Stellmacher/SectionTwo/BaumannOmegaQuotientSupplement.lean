module

public import Stellmacher.SectionTwo.LemmaTwoOne

/-!
# The native Baumann omega module in the ambient action quotient

Let `PB` be the supplied Sylow 2-subgroup of `N`, with ambient image
`B ≤ S`, where `S` is a Sylow subgroup of the finite group `G`. Assume
that the canonical native module `vSubgroup PB` maps exactly to `V` and
has noncentral Thompson action. For any surjective map `q` with kernel
`C_G(V)`, the subgroup `N.map q` has trivial 2-core. Its intersection
with the mapped ambient Sylow is exactly the nontrivial image `B.map q`.

Restrict q to N. The exact module-image equality identifies the restricted
kernel with `C_N(vSubgroup PB)`, so the native theorem (2.1) gives the
trivial core. The image of PB is Sylow in `N.map q` and lies in the
intersection with the mapped S. That intersection is itself a 2-subgroup,
so Sylow maximality gives equality. If the B-image were trivial, PB would
centralize its native module, contradicting the prescribed noncentral
Thompson action. No normality hypothesis on N is required.

Source: the native quotient and Sylow transport for the initial application
of (2.2) in Stellmacher (6.3), Journal of Algebra 190 (1997), p.31, in
`refs/latex/stellmacher-n-group.tex`. The earlier Baumann omega-supplement
construction supplies the explicit native data; V is retained throughout.
-/

namespace Stellmacher.SectionTwo
universe u

public theorem baumann_omega_quotient_supplement
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (N B V : Subgroup G) (PB : Sylow 2 N)
    (hsec : Hypotheses N)
    (hPB : (PB : Subgroup N).map N.subtype = B)
    (hBS : B ≤ (S : Subgroup G))
    (hV : (vSubgroup PB).map N.subtype = V)
    (hnot : ¬ vSubgroup PB ≤ Subgroup.centralizer
      (elementaryAbelianMaxJ (PB : Subgroup N) : Set N))
    {X : Type u} [Group X] [Finite X]
    (q : G →* X) (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.centralizer (V : Set G)) :
    pCore 2 (N.map q) = ⊥ ∧
    B.map q = ((S.mapSurjective hq : Sylow 2 X) : Subgroup X) ⊓ N.map q ∧
    B.map q ≠ ⊥ := by
  let f : N →* N.map q := q.subgroupMap N
  have hf : Function.Surjective f := q.subgroupMap_surjective N
  have hfker : f.ker = cSubgroup PB := by
    change (q.subgroupMap N).ker = _
    rw [Subgroup.ker_subgroupMap, hker]
    ext n
    change (n : G) ∈ Subgroup.centralizer (V : Set G) ↔
      n ∈ Subgroup.centralizer (vSubgroup PB : Set N)
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hn v hv
      apply Subtype.ext
      exact hn (v : G) (hV ▸ Subgroup.mem_map_of_mem N.subtype hv)
    · intro hn v hv
      rw [← hV] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      exact congrArg Subtype.val (hn w hw)
  have hcore : pCore 2 (N.map q) = ⊥ := lemma_two_one hsec PB f hf hfker
  let PB' : Sylow 2 (N.map q) := PB.mapSurjective hf
  let T : Sylow 2 X := S.mapSurjective hq
  have hPBimage : (PB' : Subgroup (N.map q)).map (N.map q).subtype = B.map q := by
    change ((PB : Subgroup N).map (q.subgroupMap N)).map (N.map q).subtype = B.map q
    rw [← hPB, Subgroup.map_map, Subgroup.map_map]
    rfl
  have hBT : B.map q ≤ (T : Subgroup X) := Subgroup.map_mono hBS
  let I : Subgroup (N.map q) := (T : Subgroup X).subgroupOf (N.map q)
  have hIp : IsPGroup 2 I :=
    T.isPGroup'.comap_of_injective (N.map q).subtype (N.map q).subtype_injective
  have hPI : (PB' : Subgroup (N.map q)) ≤ I := by
    intro x hx
    change (x : X) ∈ (T : Subgroup X)
    apply hBT
    rw [← hPBimage]
    exact Subgroup.mem_map_of_mem (N.map q).subtype hx
  have hIP : I = (PB' : Subgroup (N.map q)) := PB'.3 hIp hPI
  have hintersection : B.map q = (T : Subgroup X) ⊓ N.map q := by
    rw [← hPBimage, ← hIP]
    exact Subgroup.subgroupOf_map_subtype _ _
  refine ⟨hcore, hintersection, ?_⟩
  intro hbot
  apply hnot
  have hPBbot : (PB : Subgroup N).map f = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective
      ((PB : Subgroup N).map f) (N.map q).subtype_injective).mp
    exact hPBimage.trans hbot
  have hPBcentral : (PB : Subgroup N) ≤ Subgroup.centralizer (vSubgroup PB : Set N) := by
    have hPK := (Subgroup.map_eq_bot_iff _).mp hPBbot
    rwa [hfker] at hPK
  have hJPB : elementaryAbelianMaxJ (PB : Subgroup N) ≤ (PB : Subgroup N) :=
    sSup_le fun _ hA => hA.1
  exact Subgroup.le_centralizer_iff.mp (hJPB.trans hPBcentral)

end Stellmacher.SectionTwo
