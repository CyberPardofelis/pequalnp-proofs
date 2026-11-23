import Mathlib
import PEqualNP.Defs

-- The length of an encoded CNF formula.
--
-- `encodeCNF` writes every literal as its polarity digit, then the binary digits of its
-- variable, then an end-of-literal pair; and it writes every clause as its literals
-- followed by an end-of-clause pair. So a literal takes at least four bits, a clause takes
-- at least four bits per literal plus two, and a formula takes at least four bits per
-- literal plus two per clause.

namespace PEqualNP.Outside.Meta494

/-- The encoding of a literal is at least four bits long. -/
theorem encodeLiteral_length (l : PEqualNP.Search.Literal) :
    4 ≤ (PEqualNP.Search.encodeLiteral l).length := by
  simp only [PEqualNP.Search.encodeLiteral, List.length_append, List.length_cons,
    List.length_nil]
  omega

/-- Concatenating the encodings of the entries of a list, each at least four bits long, gives at least four bits per entry. -/
theorem flatMap_length_ge {α : Type} (xs : List α) (f : α → List Bool)
    (h : ∀ x ∈ xs, 4 ≤ (f x).length) :
    4 * xs.length ≤ (xs.flatMap f).length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha : 4 ≤ (f a).length := h a (List.mem_cons_self a xs)
      have hxs : ∀ x ∈ xs, 4 ≤ (f x).length := by
        intro x hx
        exact h x (List.mem_cons_of_mem a hx)
      have hib : 4 * xs.length ≤ (xs.flatMap f).length := ih hxs
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega

/-- The encoding of a clause is at least four bits per literal, plus two. -/
theorem encodeClause_length (c : PEqualNP.Search.Clause) :
    4 * c.length + 2 ≤ (PEqualNP.Search.encodeClause c).length := by
  have h1 : 4 * c.length ≤ (c.flatMap PEqualNP.Search.encodeLiteral).length := by
    refine flatMap_length_ge c PEqualNP.Search.encodeLiteral ?_
    intro x hx
    exact encodeLiteral_length x
  simp only [PEqualNP.Search.encodeClause, List.length_append, List.length_cons,
    List.length_nil]
  omega

/-- The length of the encoding of a formula is the sum of the lengths of the encodings of its clauses. -/
theorem encodeCNF_length (φ : PEqualNP.Search.CNF) :
    (PEqualNP.Search.encodeCNF φ).length
      = (φ.map fun c => (PEqualNP.Search.encodeClause c).length).sum := by
  simp only [PEqualNP.Search.encodeCNF]
  exact List.length_flatMap (l := φ) (f := PEqualNP.Search.encodeClause)

/-- A termwise bound on a list gives the same bound on the sum over it. -/
theorem sum_le_sum_map {α : Type} (xs : List α) (f g : α → ℕ)
    (h : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha : f a ≤ g a := h a (List.mem_cons_self a xs)
      have hxs : ∀ x ∈ xs, f x ≤ g x := by
        intro x hx
        exact h x (List.mem_cons_of_mem a hx)
      have hib : (xs.map f).sum ≤ (xs.map g).sum := ih hxs
      simp only [List.map_cons, List.sum_cons]
      omega

/-- The sum over a list of four times a value, plus two. -/
theorem sum_map_affine {α : Type} (xs : List α) (f : α → ℕ) :
    (xs.map fun x => 4 * f x + 2).sum = 4 * (xs.map f).sum + 2 * xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih]
      omega

/-- The sum over a list of a value, plus one. -/
theorem sum_map_plus_one {α : Type} (xs : List α) (f : α → ℕ) :
    (xs.map fun x => f x + 1).sum = (xs.map f).sum + xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih]
      omega

end PEqualNP.Outside.Meta494

theorem PEqualNP.Outside.L_meta_494 : ∀ φ : PEqualNP.Search.CNF, 4 * (φ.map List.length).sum + 2 * φ.length ≤ (PEqualNP.Search.encodeCNF φ).length ∧ 2 * (φ.map (fun c => c.length + 1)).sum ≤ (PEqualNP.Search.encodeCNF φ).length := by
  intro φ
  have hclause : ∀ c ∈ φ, 4 * c.length + 2 ≤ (PEqualNP.Search.encodeClause c).length := by
    intro c _
    exact PEqualNP.Outside.Meta494.encodeClause_length c
  have hsum : (φ.map fun c => (4 * c.length + 2)).sum
      ≤ (φ.map fun c => (PEqualNP.Search.encodeClause c).length).sum :=
    PEqualNP.Outside.Meta494.sum_le_sum_map φ (fun c => 4 * c.length + 2)
      (fun c => (PEqualNP.Search.encodeClause c).length) hclause
  have henc : (PEqualNP.Search.encodeCNF φ).length
      = (φ.map fun c => (PEqualNP.Search.encodeClause c).length).sum := by
    simp only [PEqualNP.Search.encodeCNF]
    exact List.length_flatMap (l := φ) (f := PEqualNP.Search.encodeClause)
  have hid : (φ.map fun c => (4 * c.length + 2)).sum
      = 4 * (φ.map List.length).sum + 2 * φ.length :=
    PEqualNP.Outside.Meta494.sum_map_affine φ List.length
  have hid2 : (φ.map (fun c => c.length + 1)).sum
      = (φ.map List.length).sum + φ.length :=
    PEqualNP.Outside.Meta494.sum_map_plus_one φ List.length
  have h1 : 4 * (φ.map List.length).sum + 2 * φ.length
      ≤ (PEqualNP.Search.encodeCNF φ).length := by
    calc 4 * (φ.map List.length).sum + 2 * φ.length
        = (φ.map fun c => (4 * c.length + 2)).sum := hid.symm
      _ ≤ (φ.map fun c => (PEqualNP.Search.encodeClause c).length).sum := hsum
      _ = (PEqualNP.Search.encodeCNF φ).length := henc.symm
  have h2 : 2 * (φ.map (fun c => c.length + 1)).sum
      ≤ (PEqualNP.Search.encodeCNF φ).length := by
    calc 2 * (φ.map (fun c => c.length + 1)).sum
        = 2 * ((φ.map List.length).sum + φ.length) := by rw [hid2]
      _ ≤ 4 * (φ.map List.length).sum + 2 * φ.length := by omega
      _ ≤ (PEqualNP.Search.encodeCNF φ).length := h1
  exact ⟨h1, h2⟩
