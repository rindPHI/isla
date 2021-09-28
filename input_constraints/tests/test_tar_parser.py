import unittest

from input_constraints.helpers import tree_to_string
from input_constraints.tests.subject_languages import tar


class TestTarParser(unittest.TestCase):
    def test_parse_example_file(self):
        with open('subject_languages/examples/single_file_tar.tar', 'r') as reader:
            content = reader.read()

        assert content is not None

        tar_parser = tar.TarParser()
        parsed_tar_parser = tar_parser.parse(content)[0]
        self.assertEqual(content, tree_to_string(parsed_tar_parser))


if __name__ == '__main__':
    unittest.main()
